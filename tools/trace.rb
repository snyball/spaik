#!/usr/bin/env ruby

# frozen_string_literal: true

# frozen_regex_literal: true

##
## Explore the output of `fuzz`
##

DOC = <<~DOCOPT
  Rust trace tools.

  Usage:
    rs-trace [--release] <bin> [<args>...]
    rs-trace fuzz [--release] [--times=<n>] <bin> <src>...
    rs-trace show <results>
    rs-trace -h | --help
    rs-trace --version

  Options:
    -h --help     Show this screen.
    --version     Show version.
    --times=<n>   How many times to run fuzzer [default: 1000]
    --release     Use release profile, debug profile is the default.
DOCOPT

require 'timeout'
require 'json'
require 'pp'
require 'rouge'
require 'colorize'
require 'docopt'

RX_AT_SRC = /^ {13}at (?<file>.+):(?<line>\d+)$/.freeze
RX_AT_FUNC = /^[ ]+(?<idx>\d+): (?<func>.+)$/.freeze
PANIC_RX = /^thread '.*' panicked at '(?<msg>.*)', (?<file>.*):(?<pos>\d+:\d+)$/.freeze

def popen(argv, timeout: nil, **kwargs, &block)
  IO.popen argv, "r+", **kwargs do |io|
    begin
      if timeout
        Timeout.timeout timeout do
          block.call(io)
          Process.wait(io.pid)
        end
      else
        block.call(io)
      end
    rescue Timeout::Error
      Process.kill(9, io.pid)
      raise
    end
  end
end

def print_around(file, center, indent: 4)
  indent = ' ' * indent
  radius = 3
  fmt = Rouge::Formatters::Terminal256.new
  lexer = Rouge::Lexers::Rust.new
  File.foreach(file).with_index do |line, num|
    num += 1
    if (num - center).abs <= radius
      line = fmt.format(lexer.lex(line.chomp))

      if num == center
        puts "#{indent}#{num.to_s.rjust(5)} > #{line}"
      else
        puts "#{indent}#{num.to_s.rjust(5)} │ #{line}"
      end
    end
    break if num - center > radius
  end
end

def with_env(**kwargs, &block)
  old_values = kwargs.map { |(var, _)| [var, ENV[var.to_s]] }.to_h
  kwargs.each { |(var, val)| ENV[var.to_s] = val.to_s }
  block.call
ensure
  old_values.each { |(var, val)| ENV[var.to_s] = val }
end

# Represents a node in a Rust backtrace
class TraceFrame
  attr_reader :func, :file, :line

  def self.build_graph(bin, inputs)
    root = TraceFrame.new(**{})
    inputs.map { |i| trim_trace(trace([bin], stdin: i)) }.each do |trace|
      root.insert(trace) if trace
    end
    root.camefrom
  end

  def self.from_trace(trace)
    root = TraceFrame.new(**{})
    root.insert(trace)
    root.camefrom.first
  end

  def collect_until_diverge
    if @from.length == 1
      [self] + @from.values.first.collect_until_diverge
    else
      [self]
    end
  end

  def puts_frame
    puts "  #{@idx}: #{@func.colorize(:light_red).bold}"
    begin
      raise Errno::ENOENT unless file
      print_around(@file, @line)
    rescue Errno::ENOENT
      puts "      Source file not available."
    end
  end

  def puts_common_trace
    collect_until_diverge.each(&:puts_frame)
  end

  def initialize(**kwargs)
    @func = kwargs[:func]
    @file = kwargs[:file]
    @line = kwargs[:line].to_i
    @idx = kwargs[:idx].to_i
    @from = {}
  end

  def camefrom
    @from.values
  end

  def to_s
    key
  end

  def insert(frames)
    root = self
    frames.each do |frame|
      root = root.add_comefrom(frame)
    end
  end

  def key
    "#{@func} [#{@file}:#{@line}]"
  end

  def add_comefrom(frame)
    key = frame.key
    @from[key] = frame unless @from.include?(key)
    @from[key]
  end
end

def collect_backtrace(io, redir: nil)
  match = io.each_line do |line|
    redir&.write line
    break true if line.chomp =~ PANIC_RX
  end

  bt_line = io.gets
  return nil unless match && bt_line && bt_line.chomp == "stack backtrace:"

  io.each_line.take_while { |line| line =~ /^  / }.map(&:chomp)
end

def parse_backtrace(bts)
  frames = []
  obj = nil
  bts.each do |line|
    line.match(RX_AT_SRC) do |m|
      raise ArgumentError("at src does not follow function") unless obj
      obj[:file] = m["file"]
      obj[:line] = m["line"]
      frames << TraceFrame.new(**obj)
      obj = nil
    end
    line.match(RX_AT_FUNC) do |m|
      obj = {
        idx: m["idx"],
        func: m["func"]
      }
    end
  end
  frames
end

def trace(tgt, stdin: nil)
  with_env(RUST_BACKTRACE: 1) do
    begin
      popen(tgt, timeout: 60, err: [:child, :out]) do |io|
        if stdin
          io.puts(stdin)
          io.close_write
        end
        bt = collect_backtrace(io, redir: $stderr)
        return parse_backtrace(bt) if bt
        return nil
      end
    rescue Timeout::Error
      warn "Timeout!"
      return nil
    end
  end
end

def begin_panic_func?(func)
  panic_funcs = ["std::panicking::begin_panic",
                 "core::panicking::panic",
                 "core::panicking::panic_fmt",
                 "std::panicking::begin_panic_fmt"]
  panic_funcs.include?(func)
end

def trim_trace(trace)
  return nil if trace.nil?
  ntrace = []
  keep = false
  trace.each do |frame|
    break if frame.func =~ /^std::rt::lang_start/
    is_begin_panic = begin_panic_func?(frame.func)
    keep ||= is_begin_panic
    next unless keep && !is_begin_panic
    ntrace << frame
  end
  ntrace
end

def show_trace(path)
  obj = JSON.parse(File.read(path))
  bin = obj["bin"]
  obj["panics"].each do |(msg, inputs)|
    next if msg == "timeout"
    puts "Building tracegraph for #{msg.dump} ..."
    puts "Trace:"
    TraceFrame.build_graph(bin, inputs).each(&:puts_common_trace)
  end
end

def fuzz(src)
  IO.popen(["radamsa"], "r+") do |io|
    io.puts(src)
    io.close_write
    io.read
  end
end

def run_fuzzed(tgt, src, num_tries: 1000)
  errors = {}

  trap "SIGINT" do
    num_tries.times do |i|
      input = fuzz(src)
      add = lambda do |key|
        errors[key] ||= []
        errors[key] << input
      end
      popen(tgt, timeout: 15, err: [:child, :out]) do |io|
        io.puts(input)
        $stderr.puts i
        io.close_write
        io.each_line do |line|
          $stderr.puts line
          _, msg, file, pos = line.match(PANIC_RX).to_a
          next unless msg
          msg.gsub!(/Ref\(0x[0-9a-z]+\)/, "Ref(...)")
          msg.gsub!(/SymID \{ id: \d+ \}/, "SymID { id: ... }")
          key = "#{msg}, #{file}:#{pos}"
          add.call key
        end
      end
    end
  end

  errors
end

def cat(*files)
  files.map { |path| File.read(path) }.join
end

def make_cargo_run_cmd(args)
  cargs = %w[cargo --color always run]
  cargs << "--release" if args["--release"]
  cargs << "--bin"
  cargs << args["<bin>"]
  cargs << "--"
  cargs += args["<args>"]
  cargs
end

if __FILE__ == $PROGRAM_NAME
  begin
    args = Docopt.docopt(DOC)
    if args["fuzz"]
      src = cat(*args["<src>"])
      res = run_fuzzed(make_cargo_run_cmd(args),
                       src,
                       num_tries: args["--times"])
      puts JSON.dump({ "bin" => args["<bin>"],
                       "panics" => res })
    elsif args["show"]
      show_trace(args["<results>"])
    else
      tb = trim_trace(trace(make_cargo_run_cmd(args)))
      TraceFrame.from_trace(tb).puts_common_trace if tb
    end
  rescue Docopt::Exit => e
    puts e.message
  end
end
