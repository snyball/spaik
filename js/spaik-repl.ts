import { Terminal } from "xterm";
import { FitAddon } from "xterm-addon-fit";
import LocalEchoController from 'local-echo';
// import ansi from 'ansi-escape-sequences';

const PROMPT: string = '> ';

function to_s(mem: ArrayBufferLike, ptr: number, sz: number) {
    const arr = new Uint8Array(mem, ptr, sz);
    return new TextDecoder().decode(arr);
}

interface SPAIKMethods {
    alloc: (sz: number) => number,
    dealloc: (ptr: number, sz: number) => void,
    repl_eval: (ptr: number, sz: number) => void,
    repl_reset: () => void,
}

interface Command {
    send: boolean;
    code: string;
}

export class SpaikRepl {
    elem: HTMLElement;
    term: Terminal;
    line_buffer: string;
    private wasm: SPAIKMethods;
    private mem: any;
    private backlog: Array<Command>;
    private ready: boolean;
    private fit_addon: FitAddon;

    constructor(elem: HTMLElement) {
        let mem: any;
        let term = new Terminal();
        const fit_addon = new FitAddon();
        term.loadAddon(fit_addon);
        term.open(elem);
        term.options.cursorBlink = true;
        fit_addon.fit();

        this.fit_addon = fit_addon;
        this.term = term;
        this.elem = elem;
        this.ready = false;
        this.backlog = [];

        let importObject = {
            imports: {},
            env: {
                abort(msg: number, file: number, line: number, column: number) {
                    console.error(`Error: ${msg} (${file}-${line}:${column})`);
                },
                console_error(ptr: number, sz: number) {
                    console.error(to_s(mem.buffer, ptr, sz))
                },
                console_log(ptr: number, sz: number) {
                    console.log(to_s(mem.buffer, ptr, sz))
                },
                xtermjs_write_stdout(ptr: number, sz: number) {
                    let s = to_s(mem.buffer, ptr, sz);
                    for (let i = 0; i < s.length; i++) {
                        if (s.charAt(i) == "\n")
                            term.write("\r");
                        term.write(s.charAt(i));
                    }
                },
            },
        };

        let inst = this;
        WebAssembly.instantiateStreaming(fetch('bin/spaik-repl.wasm'), importObject).then(obj => {
            let init = obj.instance.exports.init as CallableFunction;
            mem = obj.instance.exports.memory as any;
            inst.mem = mem;
            inst.wasm = {
                alloc: obj.instance.exports.alloc as (sz: number) => number,
                dealloc: obj.instance.exports.dealloc as (ptr: number, sz: number) => void,
                repl_eval: obj.instance.exports.repl_eval as (ptr: number, sz: number) => void,
                repl_reset: obj.instance.exports.repl_reset as () => void,
            }

            init();
        }).then(() => inst.enable());
    }

    fit() {
        this.fit_addon.fit();
    }

    enable() {
        if (this.ready) return;

        this.ready = true;
        for (let cmd of this.backlog) {
            if (cmd.send) {
                this.send_line(cmd.code)
            } else {
                this.eval(cmd.code)
            }
        }
        this.backlog = []

        let echo_ctrl = new LocalEchoController();
        this.term.loadAddon(echo_ctrl);
        echo_ctrl.setUseContinuationPrompt(false);
        let inst = this;

        function setup_read() {
            echo_ctrl.read(PROMPT).then((code: string) => {
                inst.eval(code);
                setup_read();
            })
        }
        setup_read();

    }

    send_line(code: string) {
        if (this.ready) {
            this.term.write(PROMPT);
            this.term.write(code);
            this.term.write("\r\n")
            this.eval(code);
        } else {
            this.backlog.push({
                send: true,
                code
            })
        }
    }

    reset() {
        this.wasm.repl_reset();
    }

    eval(code: string) {
        if (this.ready) {
            const arr = new TextEncoder().encode(code);
            const sz = arr.byteLength;
            const ptr = this.wasm.alloc(sz);
            const buf = new Uint8Array(this.mem.buffer, ptr, sz + 1);
            buf.set(arr);
            this.wasm.repl_eval(ptr, sz);
            this.wasm.dealloc(ptr, sz);
        } else {
            this.backlog.push({
                send: false,
                code
            });
        }
    }
}
