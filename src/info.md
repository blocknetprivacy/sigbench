# Blocknet Faraday fork Bench 2

Here is a simple explanation of what you're seeing and how it relates to the work that is
being done in the background. In the bench, press I to see this text for the current section,
and ESC to close it.

## Legacy RingCT

Today's Blocknet hides the real signer among 16 public keys: a ring of 16.

To sign, the signer must close the ring. Each step links one key to the next, and the last step
links back to the first. The comet is that loop. Each lap is one signature.

The bench times this signature so you can compare it with Faraday.

## Faraday spend

A Faraday spend is one post-quantum zk-STARK. It proves that you own a coin and can spend it. It
shows nothing about which coin.

Your coin hides among every Faraday output on the chain, not among 16. That is the goal of
Monero's FCMP++ (full-chain membership proofs). FCMP++ uses elliptic curves, which a quantum
computer can break. Faraday uses only hashes and lattices. Old Blocknet coins join the Faraday set
when they migrate.

The lattice: the ML-KEM key exchange in each output is safe because, in a large lattice, finding
a short vector is too hard, even for a quantum computer. The short arrows are such vectors.

## Argon2id 2 GiB and Argon2d 512 MiB

Argon2 is proof of work that needs memory. It fills a large memory area block by block. Each new
block mixes in an older block, and the data picks which one (the arcs).

So a miner must keep the whole area in memory. A chip with little memory cannot take a shortcut.

- 2 GiB (teal, 16 x 16): Blocknet's PoW today.
- 512 MiB (amber, 8 x 8): PoW candidate A for the fork.

## BLAKE2b-512

BLAKE2b keeps 16 words of 64 bits. One function, G, mixes 4 words at a time with only add, xor
and rotate. 12 rounds of 8 G calls make one hash.

- On the dials: a rotate turns the dial, an add sends a carry around it, and an xor flashes the
  bits that flip.
- In the columns: the 4 words of each G rise, and message words drop in from above.

PoW candidate B. It needs no memory per hash.

## SHA3-512

SHA3 (Keccak) keeps a 5 x 5 x 64 cube of bits. Each round has five steps:

- θ theta: each column mixes with its neighbors. A light sweeps across.
- ρ rho: each lane turns by its own amount. The bits spiral up.
- π pi: the lanes move to new places. The columns slide.
- χ chi: each row mixes in a nonlinear way. The rows flash.
- ι iota: a round constant goes into one lane. That lane flashes gold.

The violet lanes are the rate: input goes in and output comes out there. The blue lanes are the
capacity, which never leaves the hash. 24 rounds make one hash.

PoW candidate C. It needs no memory per hash.

## Block fold

This is FRI (Fast Reed-Solomon Interactive Oracle Proof of Proximity). FRI makes every STARK
proof small. Each fold merges 4 values into 1, so the data shrinks fast. Then the verifier checks
random paths through every layer: the gold paths. A real proof checks 106.

The block fold checks two spend proofs inside one new proof of the same size, about 770 KB.
Folds can fold again, so a whole block of spends becomes one proof.

This step needs about 11 GB of RAM. It is skipped on machines with less than 16 GB.

## Report

The bench saves these results as a plain text file next to the program, so you can send it in.
The card shows the file's path. The screen stays until you press q.
