enum Coin {
    Penny(()),
    Nickel(()),
    Dime(()),
    Quarter(())
}

fn value_in_cents(coin: Coin) -> u8 {
    match coin {
        Coin::Penny => {
			return 1;
		}
		Coin::Nickel => {
			return 5;
		}
		Coin::Dime => {
			return 10;
		}
		Coin::Quarter => {
			return 25;
		}
    }
}


fn main() {
	let x : u8 = his_money_in_cents(Person::A(Coin::Quarter(())));
}

