use rand::SeedableRng;
use rand_chacha::ChaChaRng;

pub struct RandomNumber {
    pub gen: ChaChaRng,
}

impl Default for RandomNumber {
    fn default() -> Self {
        Self::new()
    }
}

impl RandomNumber {
    pub fn new() -> Self {
        let gen = ChaChaRng::from_entropy();
        RandomNumber { gen }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::RngCore;

    #[test]
    fn generate() {
        let mut r = RandomNumber::new();
        let mut buf = [0u8; 32];
        r.gen.fill_bytes(&mut buf);
    }
}
