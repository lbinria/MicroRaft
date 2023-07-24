--------------------------- MODULE raftTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, raft, TVOperators, TraceSpec

(* Override CONSTANTS *)

(* Replace Nil constant *)
TraceNil == "null"

(* Replace Server constant *)
TraceServer ==
    ToSet(JsonTrace[1].Server)

(* Replace Value constant *)
TraceValue ==
    ToSet(JsonTrace[1].Value)

(* Can be extracted from init *)
RADefault(varName) ==
    CASE varName = "currentTerm" -> [i \in Server |-> 1]
    []  varName = "state" -> [i \in Server |-> Follower]
    []  varName = "votedFor" -> [i \in Server |-> Nil]
    []  varName = "votesResponded" -> [i \in Server |-> {}]
    []  varName = "votesGranted" -> [i \in Server |-> {}]
    []  varName = "nextIndex" -> [i \in Server |-> [j \in Server |-> 1]]
    []  varName = "matchIndex" -> [i \in Server |-> [j \in Server |-> 0]]
    []  varName = "messages" -> [m \in {} |-> 0]
    []  varName = "log" -> [i \in Server |-> << >>]
    []  varName = "commitIndex" -> [i \in Server |-> 0]

RAMapVariables(t) ==
    /\
        IF "currentTerm" \in DOMAIN t
        THEN currentTerm' = ApplyUpdates2(currentTerm, "currentTerm", t)
        ELSE TRUE
    /\
        IF "state" \in DOMAIN t
        THEN state' = ApplyUpdates2(state, "state", t)
        ELSE TRUE
    /\
        IF "votedFor" \in DOMAIN t
        THEN votedFor' = ApplyUpdates2(votedFor, "votedFor", t)
        ELSE TRUE
    /\
        IF "votesResponded" \in DOMAIN t
        THEN votesResponded' = ApplyUpdates2(votesResponded, "votesResponded", t)
        ELSE TRUE
    /\
        IF "votesGranted" \in DOMAIN t
        THEN votesGranted' = ApplyUpdates2(votesGranted, "votesGranted", t)
        ELSE TRUE
    /\
        IF "nextIndex" \in DOMAIN t
        THEN nextIndex' = ApplyUpdates2(nextIndex, "nextIndex", t)
        ELSE TRUE
    /\
        IF "matchIndex" \in DOMAIN t
        THEN matchIndex' = ApplyUpdates2(matchIndex, "matchIndex", t)
        ELSE TRUE
    /\
        IF "messages" \in DOMAIN t
        THEN messages' = ApplyUpdates2(messages, "messages", t)
        ELSE TRUE
    /\
        IF "log" \in DOMAIN t
        THEN log' = ApplyUpdates2(log, "log", t)
        ELSE TRUE
    /\
        IF "commitIndex" \in DOMAIN t
        THEN commitIndex' = ApplyUpdates2(commitIndex, "commitIndex", t)
        ELSE TRUE

(* Partial RequestVoteRequest message *)
PartialRequestVoteRequestMessage(val) ==
    LET i == val.msource
    j == val.mdest
    IN
    [mtype |-> RequestVoteRequest,
     mterm |-> IF "mterm" \in DOMAIN val THEN val.mterm ELSE currentTerm[i],
     mlastLogTerm |-> IF "mlastLogTerm" \in DOMAIN val THEN val.mlastLogTerm ELSE LastTerm(log[i]),
     mlastLogIndex |-> IF "mlastLogIndex" \in DOMAIN val THEN val.mlastLogIndex ELSE Len(log[i]),
     msource |->  i,
     mdest |-> j]

PartialEntry(val) ==
    \E i \in Server, v \in Value :
    [term  |-> IF "term" \in DOMAIN val THEN val.term ELSE currentTerm[i],
     value |-> IF "value" \in DOMAIN val THEN val.value ELSE v]

(* Remap some arguments in specific cases before apply operator *)
RAMapArgs(cur, default, op, args, eventName) ==
    (* Handle partial messages records on RequestVoteRequest *)
    (* We need to know event name and check that number of arguments are equal to 1 (one message) *)
    IF eventName = "RequestVoteRequest" /\ Len(args) = 1 THEN
        <<PartialRequestVoteRequestMessage(args[1])>>
    ELSE IF eventName = "ClientRequest" /\ Len(args) = 1 THEN
        <<PartialEntry(args[1])>>
    ELSE
        MapArgsBase(cur, default, op, args, eventName)




IsRestart ==
    /\ IsEvent("Restart")
    /\
        \/
            /\ "node" \in DOMAIN logline
            /\ Restart(logline.node)
        \/
            \E i \in Server : Restart(i)

IsTimeout ==
    /\ IsEvent("Timeout")
    /\
        \/
            /\ "node" \in DOMAIN logline
            /\ Timeout(logline.node)
        \/
            /\ \E i \in Server : Timeout(i)

IsRequestVote ==
    /\ IsEvent("RequestVoteRequest")
    /\
        \/
            /\ "event_args" \in DOMAIN logline
            /\ Len(logline.event_args) = 2
            /\ RequestVote(logline.event_args[1], logline.event_args[2])
        \/
            /\ \E i,j \in Server : RequestVote(i, j)

IsBecomeLeader ==
    /\ IsEvent("BecomeLeader")
    /\
        \/
            /\ "node" \in DOMAIN logline
            /\ BecomeLeader(logline.node)
        \/
            /\ \E i \in Server : BecomeLeader(i)

IsHandleRequestVoteRequest ==
    /\ IsEvent("HandleRequestVoteRequest")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m)

IsHandleRequestVoteResponse ==
    /\ IsEvent("HandleRequestVoteResponse")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        /\ m.mtype = RequestVoteResponse
        /\ HandleRequestVoteResponse(i, j, m)

IsUpdateTerm ==
    /\ IsEvent("UpdateTerm")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        UpdateTerm(i, j, m)

IsClientRequest ==
    /\ IsEvent("ClientRequest")
    /\
        \/
            /\ "node" \in DOMAIN logline
            /\ "val" \in DOMAIN logline
            /\ ClientRequest(logline.node, logline.val)
        \/
            /\ \E i \in Server, v \in Value : ClientRequest(i, v)

IsAppendEntries ==
    /\ IsEvent("AppendEntries")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        AppendEntries(i, j)

IsAdvanceCommitIndex ==
    /\ IsEvent("AdvanceCommitIndex")
    /\
        \/
            /\ "node" \in DOMAIN logline
            /\ AdvanceCommitIndex(logline.node)
        \/
            /\ \E i \in Server : AdvanceCommitIndex(i)

IsHandleAppendEntriesRequest ==
    /\ IsEvent("HandleAppendEntriesRequest")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)

IsHandleAppendEntriesResponse ==
    /\ IsEvent("HandleAppendEntriesResponse")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(i, j, m)

HandleRequestVoteRequestAndUpdateTerm ==
    \E m \in DOMAIN messages :
    LET i == m.msource
    j == m.mdest
    IN
    /\ m.mtype = RequestVoteRequest
    /\ HandleRequestVoteRequest(i, j, m) \cdot UpdateTerm(i, j, m)

IsHandleRequestVoteRequestAndUpdateTerm ==
    /\ IsEvent("HandleRequestVoteRequestAndUpdateTerm")
    /\ HandleRequestVoteRequestAndUpdateTerm

RATraceNext ==
    /\
        \/ IsRestart
        \/ IsTimeout
        \/ IsRequestVote
        \/ IsBecomeLeader
        \/ IsHandleRequestVoteRequest
        \/ IsHandleRequestVoteResponse
        \/ IsUpdateTerm
        \/ IsClientRequest
        \/ IsAppendEntries
        \/ IsAdvanceCommitIndex
        \/ IsHandleAppendEntriesRequest
        \/ IsHandleAppendEntriesResponse
        \/ IsHandleRequestVoteRequestAndUpdateTerm
    /\ allLogs' = allLogs \cup {log[i] : i \in Server}

TimeoutAndVoteHimself ==
    \E m1, m2 \in DOMAIN messages :
    LET i == m1.msource
    j == m1.mdest
    IN
    Timeout(i) \cdot RequestVote(i,j) \cdot HandleRequestVoteRequest(j, i, m1)
    \cdot HandleRequestVoteResponse(i, j, m2)



ComposedNext ==
    \/ HandleRequestVoteRequestAndUpdateTerm

BASE == INSTANCE raft
BaseSpec == BASE!Init /\ [][BASE!Next \/ ComposedNext]_vars

TraceAlias ==
    [
        len |-> Len(Trace),
        log     |-> <<TLCGet("level"), Trace[TLCGet("level")]>>,
        enabled |-> [
            Timeout |-> ENABLED \E i \in Server : Timeout(i),
            RequestVote |-> ENABLED \E i, j \in Server : RequestVote(i, j),
            HandleRequestVoteRequest |-> ENABLED \E m \in DOMAIN messages : m.mtype = "RequestVoteRequest" /\ HandleRequestVoteRequest(m.mdest, m.msource, m),
            HandleRequestVoteResponse |-> ENABLED \E m \in DOMAIN messages : m.mtype = "RequestVoteResponse" /\ HandleRequestVoteResponse(m.mdest, m.msource, m),
            BecomeLeader |-> ENABLED \E i \in Server : BecomeLeader(i),
            AdvanceCommitIndex |-> ENABLED \E i \in Server : AdvanceCommitIndex(i),
            Map |-> ENABLED MapVariables(Trace[TLCGet("level")])
        ]
    ]
-----------------------------------------------------------------------------
=============================================================================