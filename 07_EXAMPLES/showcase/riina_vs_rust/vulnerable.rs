// vulnerable.rs — Rust code that compiles with an information leak
//
// This compiles and runs without any warnings in Rust.
// The secret (credit card number) is printed to stdout.
// Rust has no concept of information flow control.

fn process_payment(card: String, amount: f64) -> String {
    // BUG: secret data logged to stdout — information leak!
    println!("Processing card: {}", card);

    // BUG: secret data included in log file
    eprintln!("[AUDIT] card={}, amount={}", card, amount);

    // BUG: secret data returned in public error message
    if amount <= 0.0 {
        return format!("Invalid amount for card {}", card);
    }

    format!("Charged ${:.2}", amount)
}

fn main() {
    let card = String::from("4111-1111-1111-1111");
    let result = process_payment(card, 99.99);
    println!("{}", result);
}

// $ rustc vulnerable.rs && ./vulnerable
// Processing card: 4111-1111-1111-1111     <-- LEAKED
// [AUDIT] card=4111-1111-1111-1111, amount=99.99   <-- LEAKED
// Charged $99.99
//
// Rust's type system cannot prevent this. There is no "Secret<String>" in Rust.
// The borrow checker ensures memory safety, not information flow safety.
