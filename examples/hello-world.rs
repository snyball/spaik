use spaik::Spaik;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();

    // Use exec when you don't care about the result
    vm.exec(r#"(println "Hello, World!")"#)?;

    // Use eval when you do care
    let res: String = vm.eval(r#"(println "Hello, World. Again?")"#)?;
    assert_eq!(res, "Hello, World. Again?");
    let res: spaik::Result<i32> = vm.eval(r#"(println "Hello, Wo-... This is getting old isn't it?")"#);
    assert!(res.is_err());

    // vm.exec(...) is equivalent to
    let _: spaik::Ignore = vm.eval(r#"(println "Helloooooooooooooooo?!")"#)?;

    Ok(())
}
