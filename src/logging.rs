use std::sync::Once;

static INIT: Once = Once::new();
pub fn setup_logging() {
    INIT.call_once(pretty_env_logger::init);
}
