
This fork aims to validate MicroRaft implementation against a raft specification.

# Prerequisites

- Java >= 17
- Apache maven >= 3.6
- Python >= 3.9
- TLA+ >= 1.8.0 (The Clarke release)

### Install the trace validation tools (and TLA+)

See README at https://github.com/lbinria/trace_validation_tools

### Install python librairies

The `ndjson` Python library is needed in order to perform the
validation; it can be installed with:

`pip install ndjson`

We suppose that `python` and `pip` are the commands for Python and
its package installer, if otherwise you should change the above line
and some of the following accordingly.

# Perform trace validation

To check the conformity of the trace produced by the program, the
shell scripts run_*.sh can be used:

`sh run_VotePhaseValidationTest_abstract_pipeline.sh`

It consists of the following steps:
- clean old trace files
- compile implementation of Microraft
- run a given test case of Microraft
- [merge trace files / config into one trace file (when different processes produce different trace files)]
- Run TLC on the resulting trace file

### Perform trace validation on a trace file

Alternatively, we can perform the trace validation on the obtained trace file
`trace-tla.ndjson` by using the command:

`python tla_trace_validation.py spec/AbstractRaftTrace.tla`

# Directory structure

- `spec/**`: contains Raft specification and trace specification
- `microraft/**`: contains MicroRaft implementation

____


[![Java CI with Maven](https://github.com/MicroRaft/MicroRaft/actions/workflows/maven.yml/badge.svg)](https://github.com/MicroRaft/MicroRaft/actions/workflows/maven.yml) [![CircleCI](https://dl.circleci.com/status-badge/img/gh/MicroRaft/MicroRaft/tree/master.svg?style=svg)](https://dl.circleci.com/status-badge/redirect/gh/MicroRaft/MicroRaft/tree/master) [![Integration](license-apache-2.svg)](https://github.com/MicroRaft/MicroRaft/blob/master/LICENSE)

![](microraft.io/src/img/microraft-logo.png)

# Microraft

MicroRaft is a feature-complete and stable open-source implementation of the
Raft consensus algorithm in Java. __It is a single lightweight JAR file of a few
hundred KBs of size.__ It can be used for building fault tolerant and
strongly-consistent (CP) data, metadata and coordination services. A few
examples of possible use-cases are building distributed file systems, key-value
stores, distributed lock services, etc.

MicroRaft works on top of a minimalistic and modular design. __It is a single
lightweight JAR with a few hundred KBs of size and only logging dependency.__
It contains an isolated implementation of the Raft consensus algorithm, and
a set of accompanying abstractions to run the algorithm in a multi-threaded and
distributed environment. These abstractions are defined to isolate the core
algorithm from the concerns of persistence, thread-safety, serialization,
networking, and actual state machine logic. Users are required to provide their
own implementations of these abstractions to build their custom CP distributed
systems with MicroRaft.

__Please note that MicroRaft is not a high-level solution like a distributed
key-value store or a distributed lock service. It is a core library that offers
a set of abstractions and functionalities to help you build such high-level
systems.__

## Features

MicroRaft implements the leader election, log replication, log compaction
(snapshotting), and cluster membership changes components of the Raft consensus
algorithm. Additionally, it offers a rich set of optimizations and
enhancements:

* Adaptive batching during log replication,
* Back pressure to prevent OOMEs on Raft leader and followers,
* Parallel snapshot transfer from Raft leader and followers,
* Pre-voting and leader stickiness ([Section 4.2.3 of the Raft dissertation](https://github.com/ongardie/dissertation) and [Four modifications of the Raft consensus algorithm](https://openlife.cc/system/files/4-modifications-for-Raft-consensus.pdf)),
* Auto-demotion of Raft leader on loss of quorum heartbeats [(Section 6.2 of the Raft dissertation)](https://github.com/ongardie/dissertation),
* Linearizable quorum reads without appending log entries [(Section 6.4 of the Raft dissertation)](https://github.com/ongardie/dissertation),
* Lease-based local queries on Raft leader [(Section 6.4.1 of the Raft dissertation)](https://github.com/ongardie/dissertation),
* Monotonic local queries on Raft followers [(Section 6.4.1 of the Raft dissertation)](https://github.com/ongardie/dissertation),
* Parallel disk writes on Raft leader and followers [(Section 10.2.1 of the Raft dissertation)](https://github.com/ongardie/dissertation),
* Leadership transfer [(Section 3.10 of the Raft dissertation)](https://github.com/ongardie/dissertation).
* [Improved majority quorums](https://basri.dev/posts/2020-07-27-improved-majority-quorums-for-raft/)

## Get started

See [the User Guide](https://microraft.io/docs/setup).

## Use MicroRaft in your project

Add MicroRaft to your dependency list:

```
<dependency>
    <groupId>io.microraft</groupId>
    <artifactId>microraft</artifactId>
    <version>0.5</version>
</dependency>
```

## Build from source

Pull the latest code with `gh repo clone MicroRaft/MicroRaft`
and build with `cd MicroRaft && ./mvnw clean package`.

## Source code layout

`microraft` module contains the source code of MicroRaft along with its unit
and integration test suite.

`microraft-hocon` and `microraft-yaml` modules are utility libraries for
parsing HOCON and YAML files to start Raft nodes.

`microraft-metrics` module contains the integration with the Micrometer library
for publishing MicroRaft metrics to external systems.

`afloatdb` contains a simple in-memory distributed KV store project built with MicroRaft and gRPC.

`site-src` contains the source files of [microraft.io](https://microraft.io).

## Contribute to MicroRaft

You can see [this guide](CONTRIBUTING.md) for contributing to MicroRaft.

## License

MicroRaft is available under [the Apache 2 License](https://github.com/MicroRaft/MicroRaft/blob/master/LICENSE).

MicroRaft originates from the Raft implementation that powers [Hazelcast IMDG's CP Subsystem module](https://github.com/hazelcast/hazelcast/tree/master/hazelcast/src/main/java/com/hazelcast/cp/internal/raft). You can see [the announcement](https://microraft.io/blog/2021-09-03-introducing-microraft/) for details.
