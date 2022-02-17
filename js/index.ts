import { SpaikRepl } from './spaik-repl';
export * from './spaik-repl';

let repl = new SpaikRepl(document.getElementById('terminal'));
repl.send_line('(println "Welcome to the SPAIK REPL!")');
repl.send_line('(define (fib-r a b n) (println a) (if (<= n 0) a (fib-r b (+ a b) (- n 1))))');
repl.send_line('(define (fib n) (fib-r 1 1 n))');
repl.send_line('(fib 7)');
// repl.send_line("; Try disassembling fib-r with (disassemble 'fib-r)")

window.onload = () => {
    console.log("Loaded.");
    repl.fit();
};

window.onresize = () => { repl.fit() };
