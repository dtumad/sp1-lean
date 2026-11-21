//! Independent sparse input and expected RAM values for the native export fixture.

pub const LIMIT: u64 = 1 << 48;

// The first entry at an address wins. The order is deliberately nonmonotone.
const ENTRIES: &[(u64, u8)] = &[
    (131074, 18),
    (131072, 18),
    (65536, 17),
    (65536, 99),
    (65543, 171),
    (131075, 18),
    (131071, 254),
    (131073, 18),
    (LIMIT - 1, 255),
];

pub fn word(value: u64) -> Vec<u64> {
    (0..4).map(|limb| (value >> (16 * limb)) & 0xffff).collect()
}

pub fn byte(address: u64) -> u64 {
    ENTRIES
        .iter()
        .find(|&&(key, _)| key == address)
        .map_or(0, |&(_, value)| u64::from(value))
}

pub fn value(address: u64) -> u64 {
    (0..8)
        .map(|offset| byte(address + offset) << (8 * offset))
        .sum()
}

pub fn interval(lower: u64, upper: u64, byte: u64) -> Vec<u64> {
    [word(lower), word(upper), vec![byte]].concat()
}

pub fn intervals() -> Vec<Vec<u64>> {
    // A sparse byte can only change the value at its address or the following address.
    // Keep exactly the changes in the independently evaluated public memory function.
    let mut cuts = vec![0, LIMIT];
    for &(address, _) in ENTRIES {
        for cut in [address, address + 1] {
            if cut > 0 && cut < LIMIT && byte(cut - 1) != byte(cut) {
                cuts.push(cut);
            }
        }
    }
    cuts.sort_unstable();
    cuts.dedup();
    cuts.windows(2)
        .map(|ends| interval(ends[0], ends[1], byte(ends[0])))
        .collect()
}
