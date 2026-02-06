---------------------------- MODULE proposed7_2 ----------------------------
EXTENDS TLC, Integers, FiniteSets, Randomization

CONSTANT PeersAmount

ASSUME PeersAmount \in Nat \ {0, 1}

\* プロセスの集合
IDS == 1..PeersAmount

\* 最初のリーダーは最大ID
failed_leader == PeersAmount

\* クオラムの集合
Quorum == {i \in SUBSET IDS : Cardinality(i) * 2 > Cardinality(IDS)}

\* 故障を検知したプロセスの集合
\*InitiatorSet == {i \in SUBSET IDS : Cardinality(i) * 2 > Cardinality(IDS) /\ failed_leader \notin i}
InitiatorSet == {i \in Quorum : failed_leader \notin i}

(* --algorithm bully
variables 

    \* 故障検知したプロセス
    initiators \in InitiatorSet,
    \*initiators = {1,2,3,4},

    \* リーダー以外に故障したプロセス
    others_who_failed = {},
    \*others_who_failed = {5},

    \* 次にに故障するプロセス
    possible_who_failed = IDS \ initiators,

    \* 送受信のチャンネル
    channels = [sender \in IDS |-> [receiver \in IDS \ {sender} |-> ""]],

    \* 投票の集計
    vote = [id \in IDS |-> {}],
    
    \* 現在のリーダー
    leader = [id \in IDS |-> failed_leader];
    
    \* 次のリーダー
    next_leader = [id \in IDS |-> leader[id] - 1];
    
    n = 0;
  
define 
    IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]

    MessageSenders(receiver) ==
        {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}
    
    FailedIDS == others_who_failed \* \union {failed_leader}

    WorkingIDS == IDS \ FailedIDS

    IDThatShouldBecomeNewLeader ==
        CHOOSE new_leader \in WorkingIDS : 
        \A id \in WorkingIDS \ {new_leader} : new_leader > id

    AllWorkingIDSAreCoordinatedByNewLeader ==
        \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

    EventuallySolved == []<>AllWorkingIDSAreCoordinatedByNewLeader

    SomeoneVotesMe(receiver) == \E sender \in ((WorkingIDS \intersect DOMAIN channels) \ {receiver}) :
        channels[sender][receiver] = "Vote"

end define;

fair process Peer \in IDS
begin
Initialize:
    if self \in FailedIDS then
        \* 故障したプロセスは終了
        goto Failed;
    else
        \* それ以外は通常モード
        goto NormalExecution;
    end if;

StartElection:
    if self = next_leader[self] then
        \* 次のリーダーが自分であるとき、自分に投票
        vote[self] := vote[self] \union {self};
        goto BecomeLeader;
    else
        \* そうでなければ、次のリーダー候補に投票を送信
        channels[self][next_leader[self]] := "Vote";
    end if;

CheckElectionTimeout:
    \* 次のリーダー候補も故障し、応答がない場合、IDが1つ小さいプロセスを次のリーダー候補に指名し、再選挙を行う
    if next_leader[self] \in FailedIDS then
        channels[self][next_leader[self]] := "" ||
        leader[self] := next_leader[self] ||
        next_leader[self] := next_leader[self] - 1;
        goto StartElection;
    else
        goto NormalExecution;
    end if;

BecomeLeader:
    \* 過半数の投票を得たとき、自分がリーダになり、他のプロセスにリーダーであることを通知
    if vote[self] \in Quorum then
        leader[self] := self ||
        next_leader[self] := self - 1 ||
        channels[self] := 
            [receiver \in DOMAIN channels[self] |-> 
                IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""];
    end if;

NormalExecution:
    if self \in possible_who_failed /\ self \notin others_who_failed then
        \* 送受信の度に、サーバーが故障する可能性
        either
            others_who_failed := others_who_failed \union {self} ||
            \* 接続断を通知して、相手に故障検知させる
            channels[self] := 
                [receiver \in DOMAIN channels[self] |-> 
                    IF receiver \in IDSSmallerThan[self] THEN "None" ELSE ""];
            goto Failed;
        or
            skip;
        end either;
    end if;

HandleMessage:
    with sender \in MessageSenders(self) do
        \* 投票を受信したとき、その投票をカウント
        if channels[sender][self] = "Vote" then
            vote[self] := vote[self] \union {sender} ||
            channels[sender][self] := "";
            goto BecomeLeader;
        \* リーダー通知を受信したとき、リーダーを変更
        elsif channels[sender][self] = "Leader" then
            leader[self] := sender ||
            next_leader[self] := sender - 1 ||
            channels[sender][self] := "";
            goto NormalExecution;
        \* リーダーまたは候補からの故障通知を受信         
        elsif channels[sender][self] = "None" then
            \* リーダーが故障した場合、選挙を開始
            if sender = leader[self] then
                channels[sender][self] := "";
                goto StartElection;
            \* リーダー候補が故障した場合、IDが1つ小さいプロセスを次のリーダー候補に指名して選挙
            elsif leader[self] \in FailedIDS /\ sender = next_leader[self] then
                channels[sender][self] := "" ||
                leader[self] := sender ||
                next_leader[self] := sender - 1;
                goto StartElection;
            else
                channels[sender][self] := "";
                goto NormalExecution;
            end if;
        end if;
    end with;

Failed:
    skip;
end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "ce2964c4" /\ chksum(tla) = "1911d60d")
VARIABLES initiators, others_who_failed, possible_who_failed, channels, vote, 
          leader, next_leader, n, pc

(* define statement *)
IDSSmallerThan == [id_1 \in IDS |-> {id_2 \in IDS : id_2 < id_1}]

MessageSenders(receiver) ==
    {sender \in IDS \ {receiver} : channels[sender][receiver] /= ""}

FailedIDS == others_who_failed

WorkingIDS == IDS \ FailedIDS

IDThatShouldBecomeNewLeader ==
    CHOOSE new_leader \in WorkingIDS :
    \A id \in WorkingIDS \ {new_leader} : new_leader > id

AllWorkingIDSAreCoordinatedByNewLeader ==
    \A id \in WorkingIDS : leader[id] = IDThatShouldBecomeNewLeader

EventuallySolved == []<>AllWorkingIDSAreCoordinatedByNewLeader

SomeoneVotesMe(receiver) == \E sender \in ((WorkingIDS \intersect DOMAIN channels) \ {receiver}) :
    channels[sender][receiver] = "Vote"


vars == << initiators, others_who_failed, possible_who_failed, channels, vote, 
           leader, next_leader, n, pc >>

ProcSet == (IDS)

Init == (* Global variables *)
        /\ initiators \in InitiatorSet
        /\ others_who_failed = {}
        /\ possible_who_failed = IDS \ initiators
        /\ channels = [sender \in IDS |-> [receiver \in IDS \ {sender} |-> ""]]
        /\ vote = [id \in IDS |-> {}]
        /\ leader = [id \in IDS |-> failed_leader]
        /\ next_leader = [id \in IDS |-> leader[id] - 1]
        /\ n = 0
        /\ pc = [self \in ProcSet |-> "Initialize"]

Initialize(self) == /\ pc[self] = "Initialize"
                    /\ IF self \in FailedIDS
                          THEN /\ pc' = [pc EXCEPT ![self] = "Failed"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                    /\ UNCHANGED << initiators, others_who_failed, 
                                    possible_who_failed, channels, vote, 
                                    leader, next_leader, n >>

StartElection(self) == /\ pc[self] = "StartElection"
                       /\ IF self = next_leader[self]
                             THEN /\ vote' = [vote EXCEPT ![self] = vote[self] \union {self}]
                                  /\ pc' = [pc EXCEPT ![self] = "BecomeLeader"]
                                  /\ UNCHANGED channels
                             ELSE /\ channels' = [channels EXCEPT ![self][next_leader[self]] = "Vote"]
                                  /\ pc' = [pc EXCEPT ![self] = "CheckElectionTimeout"]
                                  /\ vote' = vote
                       /\ UNCHANGED << initiators, others_who_failed, 
                                       possible_who_failed, leader, 
                                       next_leader, n >>

CheckElectionTimeout(self) == /\ pc[self] = "CheckElectionTimeout"
                              /\ IF next_leader[self] \in FailedIDS
                                    THEN /\ /\ channels' = [channels EXCEPT ![self][next_leader[self]] = ""]
                                            /\ leader' = [leader EXCEPT ![self] = next_leader[self]]
                                            /\ next_leader' = [next_leader EXCEPT ![self] = next_leader[self] - 1]
                                         /\ pc' = [pc EXCEPT ![self] = "StartElection"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                         /\ UNCHANGED << channels, leader, 
                                                         next_leader >>
                              /\ UNCHANGED << initiators, others_who_failed, 
                                              possible_who_failed, vote, n >>

BecomeLeader(self) == /\ pc[self] = "BecomeLeader"
                      /\ IF vote[self] \in Quorum
                            THEN /\ /\ channels' = [channels EXCEPT ![self] = [receiver \in DOMAIN channels[self] |->
                                                                                  IF receiver \in IDSSmallerThan[self] THEN "Leader" ELSE ""]]
                                    /\ leader' = [leader EXCEPT ![self] = self]
                                    /\ next_leader' = [next_leader EXCEPT ![self] = self - 1]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << channels, leader, next_leader >>
                      /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                      /\ UNCHANGED << initiators, others_who_failed, 
                                      possible_who_failed, vote, n >>

NormalExecution(self) == /\ pc[self] = "NormalExecution"
                         /\ IF self \in possible_who_failed /\ self \notin others_who_failed
                               THEN /\ \/ /\ /\ channels' = [channels EXCEPT ![self] = [receiver \in DOMAIN channels[self] |->
                                                                                           IF receiver \in IDSSmallerThan[self] THEN "None" ELSE ""]]
                                             /\ others_who_failed' = (others_who_failed \union {self})
                                          /\ pc' = [pc EXCEPT ![self] = "Failed"]
                                       \/ /\ TRUE
                                          /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                                          /\ UNCHANGED <<others_who_failed, channels>>
                               ELSE /\ pc' = [pc EXCEPT ![self] = "HandleMessage"]
                                    /\ UNCHANGED << others_who_failed, 
                                                    channels >>
                         /\ UNCHANGED << initiators, possible_who_failed, vote, 
                                         leader, next_leader, n >>

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ \E sender \in MessageSenders(self):
                            IF channels[sender][self] = "Vote"
                               THEN /\ /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                       /\ vote' = [vote EXCEPT ![self] = vote[self] \union {sender}]
                                    /\ pc' = [pc EXCEPT ![self] = "BecomeLeader"]
                                    /\ UNCHANGED << leader, next_leader >>
                               ELSE /\ IF channels[sender][self] = "Leader"
                                          THEN /\ /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                  /\ leader' = [leader EXCEPT ![self] = sender]
                                                  /\ next_leader' = [next_leader EXCEPT ![self] = sender - 1]
                                               /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                          ELSE /\ IF channels[sender][self] = "None"
                                                     THEN /\ IF sender = leader[self]
                                                                THEN /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                                     /\ pc' = [pc EXCEPT ![self] = "StartElection"]
                                                                     /\ UNCHANGED << leader, 
                                                                                     next_leader >>
                                                                ELSE /\ IF leader[self] \in FailedIDS /\ sender = next_leader[self]
                                                                           THEN /\ /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                                                   /\ leader' = [leader EXCEPT ![self] = sender]
                                                                                   /\ next_leader' = [next_leader EXCEPT ![self] = sender - 1]
                                                                                /\ pc' = [pc EXCEPT ![self] = "StartElection"]
                                                                           ELSE /\ channels' = [channels EXCEPT ![sender][self] = ""]
                                                                                /\ pc' = [pc EXCEPT ![self] = "NormalExecution"]
                                                                                /\ UNCHANGED << leader, 
                                                                                                next_leader >>
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Failed"]
                                                          /\ UNCHANGED << channels, 
                                                                          leader, 
                                                                          next_leader >>
                                    /\ vote' = vote
                       /\ UNCHANGED << initiators, others_who_failed, 
                                       possible_who_failed, n >>

Failed(self) == /\ pc[self] = "Failed"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << initiators, others_who_failed, 
                                possible_who_failed, channels, vote, leader, 
                                next_leader, n >>

Peer(self) == Initialize(self) \/ StartElection(self)
                 \/ CheckElectionTimeout(self) \/ BecomeLeader(self)
                 \/ NormalExecution(self) \/ HandleMessage(self)
                 \/ Failed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in IDS: Peer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in IDS : WF_vars(Peer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Nov 20 21:41:49 JST 2024 by masa1
\* Created Sat Nov 16 20:50:26 JST 2024 by masa1
