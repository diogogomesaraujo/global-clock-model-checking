// - each itm should have input, output, incomming messages, outgoing messages tapes.
// - there should be the adversary, parties and environment.
// - environment can activate a single copy of the adversary.
// - adversary can write to the incomming messages tape of all parties.
// - all parties can write to the incomming messages communication tape of the adversary.
// - all parties can write to the output-tape of their invoker and input tape of their subroutines.

module utils {
    type Round = int

    type P_Sid = int

    type Sid = A | Z | P(P_Sid) | G_Clock

    type Flag = bool
}

module uc {
    import utils.*

    type Message[msg] = { sid : Sid, message : msg }

    type ITM[in, out, in_msg, out_msg] = {
        sid                : Sid,
        input              : List[in],
        output             : List[out],
        incomming_messages : List[Message[in_msg]],
        outgoing_messages  : List[Message[out_msg]]
    }
}

module rw_clock { // in the real world clock the incomming and outgoing tapes are backdoor tapes
    import utils.*
    import uc.*

    type Input = Reg               ({ p_sid : P_Sid }) // in the paper Psid.Reg()
               | PartyRoundRequest ({ p_sid : P_Sid }) // in the paper Psid.Round()
               | RoundOk           ({ p_sid : P_Sid }) // in the paper Psid.OK()

    type Output = ()

    type Incoming = AdversaryRoundRequest ({ sid : Sid }) // in the paper Sim.Round() but adapted to the real world model
                   | Corrupt               ({ p_sid : P_Sid }) // note: modelling corruptions like Universally Composable Synchronous Computation instead

    type Outgoing = AdversaryRoundResponse ({ round : Round }) // in the paper r
                  | AdversaryOk            ({ p_sid : P_Sid }) // in the paper Sim(Psid.OK)

    type ClockITM = ITM[Input, Output, Incoming, Outgoing]

    type ClockState = {
        current_round      : Round,        // in the paper r
        registered_parties : Set[P_Sid],   // in the paper Reg
        corrupted_parties  : Set[P_Sid],   // in the paper C
        done               : P_Sid -> Flag // in the paper Done
    }
}

module rw_adversary {
    import utils.*
    import uc.*

    type Input = Corrupt ({ p_sid : P_Sid })

    type Output = ()

    type Incoming = RoundResponse ({ round : Round })
                   | Ok ({ p_sid : P_Sid })

    type Outgoing = RoundRequest ({ sid : Sid })

    type AdversaryITM = ITM[Input, Output, Incoming, Outgoing]

    type AdversaryState = { 
        parties_that_oked : Set[P_Sid],
        corrupted_parties : Set[P_Sid]
    }
}

module rw_environment {
    import utils.*
    import uc.*

    type Input = ()

    type Output = Corrupted          ({ p_sid : P_Sid })
                | Ok                 ({ p_sid : P_Sid }) // in the paper ok
                | PartyRoundResponse ({ round: Round })  // in the paper r
                | Failed             ({ p_sid : P_Sid }) // in the paper ⊥

    type Incoming = ()

    type Outgoing = ()

    type EnvironmentITM = ITM[Input, Output, Incoming, Outgoing]
}

module rw_party {
    import utils.*
    import uc.*

    type Input = RoundResponse ({ round : Round }) // in the paper Psid.Round()
               | Ok                                // in the paper Psid.OK()

    type Output = ()

    type Incoming = ()

    type Outgoing = ()

    type PartyITM = ITM[Input, Output, Incoming, Outgoing]
}

module rw {
    import utils.*
    
}