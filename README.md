<div align="center">
  <h3 align="center">global-clock-model-checking</h3>
  <p align="center">
    Model Checking the UC-realization of the Global Clock Ideal Functionality in Quint
  </p>
</div>

## About 

This project is being developed as part of my MsC thesis in Computer Science at Faculdade de Ciências da Universidade do Porto, entitled _"From Ideal Clocks to Buildable Ones"_. 

## UC-framework in Quint

In Quint, we model each machine as a state record with input, output, and incoming-message tapes. Depending on if a machine is a child/parent of another one, or if it corresponds to a global functionality, it has different rules for which machines can it write to and who can to it.

### Read/Write rules
- The environment can write to the parties’ input tapes, and parties can write to the environment’s output tape.
- The simulator can write to the parties’ incoming-message tapes. Conversely, parties can write to the simulator’s incoming-message tape, modeling leakage.
- Parties can write to the global functionality’s input tape, and the functionality can write to the parties’ output tapes.

## Ideal World

The ideal-world model has four main components:
- Environment (Z): Registers parties and requests rounds or OK (on behalf of them).
- G-Clock: Tracks registered parties, corruptions, readiness, and the current round.
- Simulator (S): Requests round advances and party corruptions.
- Parties (P): Forward requests to the clock and return its responses.

### G-Clock

The G-Clock model is based on the _Crossing with Confidence: Formal Analysis and Model Checking of Blockchain Bridges_ paper. For party corruption, the adaptive-corruption approach from _Universally Composable Synchronous Computation_ was followed, where parties can be corrupted during execution rather than being fixed as corrupted from the start.

The clock maintains a round counter, a set of registered parties, a set of corrupted parties, and a readiness flag (done) for each party.

```
INITIALIZE:
    current_round := 0
    registered_parties := {}
    corrupted_parties := {}
    done := {}

ENVIRONMENT Z:
    After all parties register, send REG, ROUND, or OK requests.
    Record party responses; clear round observations on OK.

PARTY p:
    Forward Z's requests to G-Clock.
    Forward G-Clock's responses to Z.

G-CLOCK:
    On REG(p):
        register p if new; initialize done[p] := false
        return REGISTER_OK

    On ROUND(p):
        return current_round

    On OK(p):
        if p is not registered: return FAILED
        if all registered, uncorrupted parties are ready
           after counting p's OK:
            reset their readiness flags
            advance current_round (up to MaxRound)
        else:
            mark p ready
            send OK(p) leakage to the simulator
            return ROUND_OK

SIMULATOR S:
    When tapes are empty, may request a clock round
    or corrupt a party, up to CorruptedBound.
    Round requests and corruption requests are forwarded
    to G-Clock; OK leakage is recorded.

G-CLOCK ON SIMULATOR MESSAGES:
    ROUND   -> return current_round to simulator
    CORRUPT(p) -> add p to corrupted_parties
```

### Properties

To prove the G-Clock's correctness, the following properties where checked (mostly based on the _Crossing with Confidence: Formal_ paper).

#### Time Agreement

*If two parties query the time and no OK requests have been sent in the middle then G-clock responds with the same time.*

Bounds used:
- Parties: 3
- Corrupted: 1
- Rounds: 5

No violations found.

## Real World

Work in progress.


## References
- [UC framework and rules](https://swayam-padhy.gitbook.io/)
- [GClock Model Cheching](https://eprint.iacr.org/2026/292.pdf)
- [UC Synchrony and adaptive corruption](https://eprint.iacr.org/2011/310.pdf)
- [Quint cheatsheet](https://quint.sh/quint-cheatsheet.pdf)
