use spaik::Spaik;

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut vm = Spaik::new();

    // Use exec when you don't care about the result
    vm.exec(r#"(println "Hello, World!")"#)?;

    vm.set("*global*", 3);
    // Use eval when you do care
    let res: i32 = vm.eval(r#"(+ 1 *global*)"#)?;
    assert_eq!(res, 4);

    Ok(())
}
