import { SpaikRepl } from './spaik-repl';
export * from './spaik-repl';

let repl = new SpaikRepl(document.getElementById('terminal'));

export function repl_fib_example() {
    repl.send_line('(println "Welcome to the SPAIK REPL!")');
    repl.send_line('(define (fib-r a b n) (println a) (if (<= n 0) a (fib-r b (+ a b) (- n 1))))');
    repl.send_line('(define (fib n) (fib-r 1 1 n))');
    repl.send_line('(fib 7)');
}

export function repl_disassemble_example() {
    repl.send_line("(disassemble 'max)");
    repl.send_line("(max '(3 2 1 22 3 100 2 3))")
}

window.onresize = () => { repl.fit() };
window.onload = () => {
    repl.fit()
    repl_fib_example();
}
