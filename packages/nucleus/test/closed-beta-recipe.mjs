// Version-specific authority-free fixture. Rust's sole sealed-recipe decoder
// still decides whether these bytes are canonical and whether replay succeeds.
export const CLOSED_BETA_RECIPE = new Uint8Array([
  6, 0, 11, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 1, 4, 53, 0, 2, 0,
  3, 56, 0, 4, 0, 5, 6, 0, 6, 7, 1, 0, 4, 100, 101, 109, 111, 9, 0, 8, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 4, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0,
]);
