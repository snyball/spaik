#[cfg(test)]
mod tests {
    use crate::Spaik;

    #[test]
    fn eval_macroexpand_eval() {
        let mut vm = Spaik::new();
        vm.exec(r#"(define n 0)"#).unwrap();
        vm.exec(r#"(eval-when-compile (inc! n))"#).unwrap();
        let n: i32 = vm.eval(r#"n"#).unwrap();
        assert_eq!(n, 1);
    }
}
