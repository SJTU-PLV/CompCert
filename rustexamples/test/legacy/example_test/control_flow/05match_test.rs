enum Coin {
    Penny(()),
    Nickel(()),
    Dime(()),
    Quarter(())
}

// error! Incomplete struct or variant Person
enum Person {
    A(Coin),
    B(Coin)
}


fn his_money_in_cents(p: Person) -> u8 {
    match p {
        A(Penny(_)) => {
            return 1
        }
        A(Nickel(_)) => {
            return 5
        }
        A(Dime(_)) => {
            return 10
        }
        A(Quarter(_)) => {
            return 25
        }
        B(Penny(_)) => {
            return 2
        }
        B(Nickel(_)) => {
            return 10
        }
        B(Dime(_)) => {
            return 20
        }
        B(Quarter(_)) => {
            return 50
        }
    }
}


fn main() {
	let x : u8 = his_money_in_cents(Person::A(Coin::Quarter(())));
}

