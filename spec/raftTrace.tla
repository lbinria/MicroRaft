--------------------------- MODULE raftTrace ---------------------------

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
        THEN currentTerm' = MapVariable(currentTerm, "currentTerm", t)
        ELSE TRUE
    /\
        IF "state" \in DOMAIN t
        THEN state' = MapVariable(state, "state", t)
        ELSE TRUE
    /\
        IF "votedFor" \in DOMAIN t
        THEN votedFor' = MapVariable(votedFor, "votedFor", t)
        ELSE TRUE
    /\
        IF "votesResponded" \in DOMAIN t
        THEN votesResponded' = MapVariable(votesResponded, "votesResponded", t)
        ELSE TRUE
    /\
        IF "votesGranted" \in DOMAIN t
        THEN votesGranted' = MapVariable(votesGranted, "votesGranted", t)
        ELSE TRUE
    /\
        IF "nextIndex" \in DOMAIN t
        THEN nextIndex' = MapVariable(nextIndex, "nextIndex", t)
        ELSE TRUE
    /\
        IF "matchIndex" \in DOMAIN t
        THEN matchIndex' = MapVariable(matchIndex, "matchIndex", t)
        ELSE TRUE
    /\
        IF "messages" \in DOMAIN t
        THEN messages' = MapVariable(messages, "messages", t)
        ELSE TRUE
    /\
        IF "log" \in DOMAIN t
        THEN log' = MapVariable(log, "log", t)
        ELSE TRUE
    /\
        IF "commitIndex" \in DOMAIN t
        THEN commitIndex' = MapVariable(commitIndex, "commitIndex", t)
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

PartialAppendEntriesRequest(val) ==
    LET
    i == val.msource
    j == val.mdest
    prevLogIndex == nextIndex[i][j] - 1
    prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
    \* Send up to 1 entry, constrained by the end of the log.
    lastEntry == Min({Len(log[i]), nextIndex[i][j]})
    entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
    IN
    [mtype |-> AppendEntriesRequest,
    mterm |-> IF "mterm" \in DOMAIN val THEN val.mterm ELSE currentTerm[i],
    mprevLogIndex |-> IF "mprevLogIndex" \in DOMAIN val THEN val.mprevLogIndex ELSE prevLogIndex,
    mprevLogTerm  |-> IF "mprevLogTerm" \in DOMAIN val THEN val.mprevLogTerm ELSE prevLogTerm,
    mentries |-> IF "mentries" \in DOMAIN val THEN val.mentries ELSE entries,
    mcommitIndex |-> IF "mcommitIndex" \in DOMAIN val THEN val.mcommitIndex ELSE Min({commitIndex[i], lastEntry}),
    msource        |-> i,
    mdest          |-> j
    ]


PartialEntry(val) ==
    \E i \in Server, v \in Value :
    [term  |-> IF "term" \in DOMAIN val THEN val.term ELSE currentTerm[i],
     value |-> IF "value" \in DOMAIN val THEN val.value ELSE v]

(* Remap some arguments in specific cases before apply operator *)
RAMapArgs(mapFunction, cur, default, op, args, eventName) ==
    (* Handle partial messages records on RequestVoteRequest *)
    (* We need to know event name and check that number of arguments are equal to 1 (one message) *)
    IF mapFunction = "PartialRequestVoteRequestMessage" THEN
        <<PartialRequestVoteRequestMessage(args[1])>>
    ELSE IF mapFunction = "PartialEntry" THEN
        <<PartialEntry(args[1])>>
    ELSE IF mapFunction = "PartialAppendEntriesRequest" THEN
        <<PartialAppendEntriesRequest(args[1])>>
    ELSE
        MapArgsBase(mapFunction, cur, default, op, args, eventName)




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
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            RequestVote(logline.event_args[1], logline.event_args[2])
        ELSE
            \E i, j \in Server : RequestVote(i, j)

IsBecomeLeader ==
    /\ IsEvent("BecomeLeader")
    /\
        (* Optimizations *)
        IF "state" \in DOMAIN logline /\ Len(logline.state) = 1 /\ logline.state[1].op = "Replace" THEN
            BecomeLeader(logline.state[1].path[1])
        ELSE
            \E i \in Server : BecomeLeader(i)

IsHandleRequestVoteRequest ==
    /\ IsEvent("HandleRequestVoteRequest")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            \E m \in DOMAIN messages :
                /\ m.mtype = RequestVoteRequest
                /\ m.mdest = logline.event_args[1]
                /\ m.msource = logline.event_args[2]
                /\ HandleRequestVoteRequest(logline.event_args[1], logline.event_args[2], m)
        ELSE
            \E m \in DOMAIN messages : /\ m.mtype = RequestVoteRequest /\ HandleRequestVoteRequest(m.mdest, m.msource, m)

IsHandleRequestVoteResponse ==
    /\ IsEvent("HandleRequestVoteResponse")
    /\ \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource IN
        /\ m.mtype = RequestVoteResponse
        /\ HandleRequestVoteResponse(i, j, m)

IsUpdateTerm ==
    /\ IsEvent("UpdateTerm")
    /\ \E m \in DOMAIN messages : UpdateTerm(m.mdest, m.msource , m)

IsClientRequest ==
    /\ IsEvent("ClientRequest")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            ClientRequest(logline.event_args[1], logline.event_args[2])
        ELSE
            \E i \in Server, v \in Value : ClientRequest(i, v)

IsAppendEntries ==
    /\ IsEvent("AppendEntries")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            AppendEntries(logline.event_args[1], logline.event_args[2])
        ELSE
            \E i, j \in Server : AppendEntries(i, j)

IsAdvanceCommitIndex ==
    /\ IsEvent("AdvanceCommitIndex")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 1 THEN
            AdvanceCommitIndex(logline.event_args[1])
        ELSE
            \E i \in Server : AdvanceCommitIndex(i)


IsHandleAppendEntriesRequest ==
    /\ IsEvent("HandleAppendEntriesRequest")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            \E m \in DOMAIN messages :
                /\ m.mtype = AppendEntriesRequest
                /\ m.mdest = logline.event_args[1]
                /\ m.msource = logline.event_args[2]
                /\ HandleAppendEntriesRequest(logline.event_args[1], logline.event_args[2], m)
        ELSE
            \E m \in DOMAIN messages :
                /\ m.mtype = AppendEntriesRequest
                /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)


IsHandleAppendEntriesResponse ==
    /\ IsEvent("HandleAppendEntriesResponse")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) = 2 THEN
            \E m \in DOMAIN messages :
                /\ m.mtype = AppendEntriesResponse
                /\ m.mdest = logline.event_args[1]
                /\ m.msource = logline.event_args[2]
                /\ HandleAppendEntriesResponse(logline.event_args[1], logline.event_args[2], m)
        ELSE
            \E m \in DOMAIN messages :
                /\ m.mtype = AppendEntriesResponse
                /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)

HandleRequestVoteRequestAndUpdateTerm ==
    \E m \in DOMAIN messages :
        LET i == m.mdest
        j ==  m.msource
        IN
        /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m) \cdot UpdateTerm(i, j, m)

HandleAppendEntriesRequestAndUpdateTerm ==
    \E m \in DOMAIN messages :
        LET i == m.mdest
        j == m.msource
        IN
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m) \cdot UpdateTerm(i, j, m)

IsHandleRequestVoteRequestAndUpdateTerm ==
    /\ IsEvent("HandleRequestVoteRequestAndUpdateTerm")
    /\ HandleRequestVoteRequestAndUpdateTerm

IsHandleAppendEntriesRequestAndUpdateTerm ==
    /\ IsEvent("HandleAppendEntriesRequestAndUpdateTerm")
    /\ HandleAppendEntriesRequestAndUpdateTerm

RATraceNext ==
    /\
        \/ IsRestart
        \/ IsTimeout
        \/ IsRequestVote
        \/ IsBecomeLeader
        \/ IsHandleRequestVoteRequestAndUpdateTerm
        \/ IsHandleRequestVoteRequest
        \/ IsHandleRequestVoteResponse
        \/ IsUpdateTerm
        \/ IsClientRequest
        \/ IsAppendEntries
        \/ IsAdvanceCommitIndex
        \/ IsHandleAppendEntriesRequestAndUpdateTerm
        \/ IsHandleAppendEntriesRequest
        \/ IsHandleAppendEntriesResponse

    /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\*TimeoutAndVoteHimself ==
\*    \E m1, m2 \in DOMAIN messages :
\*    LET i == m1.msource
\*    j == m1.mdest
\*    IN
\*    Timeout(i) \cdot RequestVote(i,j) \cdot HandleRequestVoteRequest(j, i, m1)
\*    \cdot HandleRequestVoteResponse(i, j, m2)

ComposedNext ==
    \/ HandleRequestVoteRequestAndUpdateTerm
    \/ HandleAppendEntriesRequestAndUpdateTerm

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
            HandleAppendEntriesRequest |-> ENABLED \E m \in DOMAIN messages : m.mtype = "AppendEntriesRequest" /\ HandleAppendEntriesRequest(m.mdest, m.msource, m),
            HandleAppendEntriesResponse |-> ENABLED \E m \in DOMAIN messages : m.mtype = "AppendEntriesResponse" /\ HandleAppendEntriesResponse(m.mdest, m.msource, m),
            HandleAppendEntriesResponse2 |-> ENABLED \E m \in DOMAIN messages : m.mtype = "AppendEntriesResponse" /\ m.msuccess /\ m.mterm = currentTerm[m.mdest] /\ m.mmatchIndex = 1 /\ HandleAppendEntriesResponse(m.mdest, m.msource, m),
            BecomeLeader |-> ENABLED \E i \in Server : BecomeLeader(i),
            AdvanceCommitIndex |-> ENABLED \E i \in Server : AdvanceCommitIndex(i),
            Map |-> ENABLED MapVariables(Trace[TLCGet("level")])
        ]
    ]
-----------------------------------------------------------------------------
=============================================================================