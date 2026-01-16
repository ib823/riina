// Standalone test to debug field inversion
// Compile: rustc --edition 2021 test_inversion.rs
// Run: ./test_inversion

fn main() {
    println!("Testing field element inversion...");

    // Test 1: Verify that 0 + 0 = 0
    let zero = FieldElement::ZERO;
    let sum = zero + zero;
    println!("0 + 0 = {:?}", sum);
    println!("is_zero: {}", sum.is_zero());

    // Test 2: Verify that 1 * 1 = 1
    let one = FieldElement::ONE;
    let product = one * one;
    println!("\n1 * 1 = {:?}", product);
    println!("equals 1: {}", product == one);

    // Test 3: Simple inversion
    let two = FieldElement::from_i64(2);
    println!("\ntwo = {:?}", two);
    let two_inv = two.invert();
    println!("two_inv = {:?}", two_inv);
    let should_be_one = two * two_inv;
    println!("2 * 2^(-1) = {:?}", should_be_one);
    println!("equals 1: {}", should_be_one == one);

    // Debug: Check intermediate step
    let two_squared = two.square();
    println!("\nDEBUG: 2^2 = {:?}", two_squared);
    println!("DEBUG: 2^2 == 4? {}", two_squared == FieldElement::from_i64(4));

    // Test 4: Invert(1) should be 1
    let one_inv = one.invert();
    println!("\n1^(-1) = {:?}", one_inv);
    println!("equals 1: {}", one_inv == one);

    // Test 5: Known test vector
    // For p = 2^255 - 19, the element 9 is the basepoint u-coordinate
    let nine = FieldElement::from_i64(9);
    let nine_inv = nine.invert();
    let should_be_one2 = nine * nine_inv;
    println!("\n9 * 9^(-1) = {:?}", should_be_one2);
    println!("equals 1: {}", should_be_one2 == one);
}

// Minimal FieldElement implementation for testing
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FieldElement {
    limbs: [i64; 5],
}

impl FieldElement {
    const ZERO: Self = Self { limbs: [0, 0, 0, 0, 0] };
    const ONE: Self = Self { limbs: [1, 0, 0, 0, 0] };

    fn from_i64(value: i64) -> Self {
        Self { limbs: [value, 0, 0, 0, 0] }.reduce()
    }

    fn is_zero(&self) -> bool {
        self.ct_eq(&Self::ZERO) == 1
    }

    fn ct_eq(&self, other: &Self) -> i64 {
        let a = self.reduce();
        let b = other.reduce();
        let mut diff = 0i64;
        for i in 0..5 {
            diff |= a.limbs[i] ^ b.limbs[i];
        }
        let zero = (diff | -diff) >> 63;
        (zero + 1) & 1
    }

    fn weak_reduce(self) -> Self {
        let mut limbs = self.limbs;
        let c0 = limbs[0] >> 51;
        limbs[0] &= 0x7ffffffffffff;
        limbs[1] += c0;
        let c1 = limbs[1] >> 51;
        limbs[1] &= 0x7ffffffffffff;
        limbs[2] += c1;
        let c2 = limbs[2] >> 51;
        limbs[2] &= 0x7ffffffffffff;
        limbs[3] += c2;
        let c3 = limbs[3] >> 51;
        limbs[3] &= 0x7ffffffffffff;
        limbs[4] += c3;
        let c4 = limbs[4] >> 51;
        limbs[4] &= 0x7ffffffffffff;
        limbs[0] += c4 * 19;
        Self { limbs }
    }

    fn reduce(self) -> Self {
        let mut fe = self.weak_reduce();
        fe = fe.weak_reduce();
        let mut limbs = fe.limbs;
        let mut borrow: i64 = 0;
        let mut result = [0i64; 5];
        result[0] = limbs[0] - 0x7ffffffffffed + borrow;
        borrow = result[0] >> 63;
        result[0] &= 0x7ffffffffffff;
        for i in 1..5 {
            result[i] = limbs[i] - 0x7ffffffffffff + borrow;
            borrow = result[i] >> 63;
            result[i] &= 0x7ffffffffffff;
        }
        let mask = borrow;
        for i in 0..5 {
            limbs[i] = (limbs[i] & mask) | (result[i] & !mask);
        }
        Self { limbs }
    }

    fn square(self) -> Self {
        self * self
    }

    fn invert(self) -> Self {
        debug_assert!(!self.is_zero(), "Cannot invert zero");

        let z2 = self.square();
        println!("  z2 (x^2) = {:?}", z2);
        let z9 = z2.square().square() * self;
        println!("  z9 (x^9) = {:?}", z9);
        let z11 = z9 * z2;
        println!("  z11 (x^11) = {:?}", z11);
        let z2_5_0 = z11.square() * z9;  // FIX: Only square once!
        println!("  z2_5_0 (x^31) = {:?}", z2_5_0);

        let mut t = z2_5_0;
        for _ in 0..5 {
            t = t.square();
        }
        let z2_10_0 = t * z2_5_0;
        println!("  z2_10_0 (x^(2^10-1)) = {:?}", z2_10_0);

        t = z2_10_0;
        for _ in 0..10 {
            t = t.square();
        }
        let z2_20_0 = t * z2_10_0;
        println!("  z2_20_0 (x^(2^20-1)) = {:?}", z2_20_0);

        t = z2_20_0;
        for _ in 0..20 {
            t = t.square();
        }
        let z2_40_0 = t * z2_20_0;
        println!("  z2_40_0 (x^(2^40-1)) = {:?}", z2_40_0);

        t = z2_40_0;
        for _ in 0..10 {
            t = t.square();
        }
        let z2_50_0 = t * z2_10_0;
        println!("  z2_50_0 (x^(2^50-1)) = {:?}", z2_50_0);

        t = z2_50_0;
        for _ in 0..50 {
            t = t.square();
        }
        let z2_100_0 = t * z2_50_0;
        println!("  z2_100_0 (x^(2^100-1)) = {:?}", z2_100_0);

        t = z2_100_0;
        for _ in 0..100 {
            t = t.square();
        }
        let z2_200_0 = t * z2_100_0;
        println!("  z2_200_0 (x^(2^200-1)) = {:?}", z2_200_0);

        t = z2_200_0;
        for _ in 0..50 {
            t = t.square();
        }
        let z2_250_0 = t * z2_50_0;
        println!("  z2_250_0 (x^(2^250-1)) = {:?}", z2_250_0);

        t = z2_250_0;
        for _ in 0..5 {
            t = t.square();
        }
        t = t * z11;
        println!("  Final (x^(2^255-21)) = {:?}", t);

        t
    }
}

impl std::ops::Add for FieldElement {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let limbs = [
            self.limbs[0] + rhs.limbs[0],
            self.limbs[1] + rhs.limbs[1],
            self.limbs[2] + rhs.limbs[2],
            self.limbs[3] + rhs.limbs[3],
            self.limbs[4] + rhs.limbs[4],
        ];
        Self { limbs }.weak_reduce()
    }
}

impl std::ops::Sub for FieldElement {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let limbs = [
            self.limbs[0] - rhs.limbs[0] + 2 * 0x7ffffffffffed,
            self.limbs[1] - rhs.limbs[1] + 2 * 0x7ffffffffffff,
            self.limbs[2] - rhs.limbs[2] + 2 * 0x7ffffffffffff,
            self.limbs[3] - rhs.limbs[3] + 2 * 0x7ffffffffffff,
            self.limbs[4] - rhs.limbs[4] + 2 * 0x7ffffffffffff,
        ];
        Self { limbs }.weak_reduce()
    }
}

impl std::ops::Mul for FieldElement {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let a = self.limbs;
        let b = rhs.limbs;
        let mut c = [0i128; 10];
        for i in 0..5 {
            for j in 0..5 {
                c[i + j] += i128::from(a[i]) * i128::from(b[j]);
            }
        }
        for i in 0..5 {
            c[i] += c[i + 5] * 19;
        }
        let limbs = [
            c[0] as i64,
            c[1] as i64,
            c[2] as i64,
            c[3] as i64,
            c[4] as i64,
        ];
        Self { limbs }.weak_reduce().weak_reduce()
    }
}
