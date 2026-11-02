# Blocknet Faraday fork Bench 3

Here is a simple explanation of what you're seeing and how it relates to the work that is
being done in the background. In the bench, press I to see this text for the current section,
and ESC to close it.

## Legacy RingCT

Today's Blocknet hides the real signer among 16 public keys: a ring of 16.

To sign, the signer must close the ring. Each step links one key to the next, and the last step
links back to the first. The comet is that loop. Each lap is one signature.

The bench times this signature so you can compare it with the new spend proof.

## zk-VOLEitH spend

A spend is one post-quantum zero-knowledge proof. It proves that you own the coins you spend,
that each coin is in the set, that the nullifiers are correct, and that the amounts balance.
It shows nothing about which coins, how much, or who owns them.

It is not a STARK. It is VOLE-in-the-Head, the method of the FAEST signature. It uses only AES
and hashes. There is no trusted setup and no fold: each transaction carries its own proof.

The tree: the prover grows 11 trees of random values from seeds. The verifier gets every leaf
but one in each tree. The hidden leaves mask the secret values, so the proof checks every AES
round and every sum without seeing them.

The bench runs 4 shapes: 2, 4, 8 and 16 inputs, each with the same number of outputs.

## BLAKE2b-512

BLAKE2b keeps 16 words of 64 bits. One function, G, mixes 4 words at a time with only add, xor
and rotate. 12 rounds of 8 G calls make one hash.

- On the dials: a rotate turns the dial, an add sends a carry around it, and an xor flashes the
  bits that flip.
- In the columns: the 4 words of each G rise, and message words drop in from above.

The Faraday proof of work, personalization blocknet/pow/v1. It needs no memory per hash.

## Anonymity set

Your coin hides among 2^20 = 1,048,576 coins, not among 16. Today that is every coin on the
chain. Each coin is a hidden commitment to its owner key and amount (80 bytes).

The proof picks the coin with two short selectors of 45 bits, one for each axis of the grid.
They cross at one coin. The verifier adds up the whole set with the selectors still hidden, so it
learns that some coin was opened, but not which one.

The ML-KEM-768 note in each output is lattice-based. It lets the receiver find the coin.

## Report

The bench saves these results as a plain text file next to the program, so you can send it in.
The card shows the file's path. The screen stays until you press q.
