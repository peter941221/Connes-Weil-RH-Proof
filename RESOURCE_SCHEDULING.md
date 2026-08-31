# Resource Scheduling

Status: active from 2026-08-31.

## 1. What It Is

All WSL research commands use `scripts/run_resource_aware_task.sh`.  The
runner assigns one of two resource classes and then acquires two locks:

```text
                           +----------------------+
command + WSL snapshot --> | static + dynamic     |
                           | classifier           |
                           +----------+-----------+
                                      |
                         +------------+------------+
                         |                         |
                  normal / shared           heavy / exclusive
                         |                         |
                         +------------+------------+
                                      |
                           +----------v-----------+
                           | per-mirror exclusive |
                           | .lake/build lock     |
                           +----------+-----------+
                                      |
                           +----------v-----------+
                           | run command          |
                           +----------------------+
```

The global resource lock coordinates CPU and memory use across
`/home/peter/rh` and `/home/peter/rh-cert`.  The per-mirror lock prevents two
Lake processes from writing the same `.lake/build` tree.  All participants
must run in the same `Ubuntu-24.04` WSL distro and keep the default
`RH_RESOURCE_LOCK_DIR`, or point that variable to the same directory.

## 2. Why It Exists

Two focused warm Lean builds can use separate mirrors at the same time.  A
full build or a NumPy/SciPy certificate run can consume the WSL VM's available
CPU and memory.  Starting another job during that interval increases elapsed
time and can trigger swapping or process termination.

The runner preserves useful concurrency while giving an all-resource job an
empty field.  An admission lock also gives a queued heavy job priority over
new normal jobs.  Without that admission step, a stream of shared holders can
starve an exclusive holder.

## 3. Classification Policy

The classifier fails closed: an unknown command starts as `heavy`.  A static
heavy rule cannot be downgraded with `--class normal`.

```text
+----------------------------------------------+--------+---------------------+
| Observed command                             | Class  | Reason              |
+----------------------------------------------+--------+---------------------+
| Warm Lake build, 1-4 explicit leaf targets   | normal | bounded rebuild     |
| Focused `lake env lean FILE`                 | normal | one-file probe      |
| rg/sed/cat/hash and local Git operations     | normal | low CPU and memory  |
| Cold Lean mirror                             | heavy  | dependency wave     |
| `lake build` with no explicit target         | heavy  | root/default wave   |
| Root, aggregate, or more than four targets   | heavy  | broad elaboration   |
| `lake clean` or `lake update`                | heavy  | cache/dependency IO |
| NumPy/SciPy/probe/sweep/train/benchmark      | heavy  | BLAS/worker fanout  |
| Git clone/fetch/gc/repack/submodule/lfs      | heavy  | object-store IO     |
| Opaque shell payload or unknown command      | heavy  | no safe cost bound  |
+----------------------------------------------+--------+---------------------+
```

The runner then upgrades a `normal` decision to `heavy` when one of these WSL
signals crosses its threshold:

```text
+----------------------------------+---------+-----------------------------------+
| Signal                           | Default | Override                          |
+----------------------------------+---------+-----------------------------------+
| MemAvailable                     | < 6 GiB | RH_RESOURCE_MIN_AVAILABLE_GIB     |
| MemAvailable / MemTotal          | < 20%   | RH_RESOURCE_MIN_AVAILABLE_PERCENT |
| one-minute load / logical CPUs   | > 0.70  | RH_RESOURCE_MAX_SHARED_LOAD_RATIO |
+----------------------------------+---------+-----------------------------------+
```

These measurements govern admission for managed jobs.  They do not stop an
unmanaged Windows or WSL process.  Check Task Manager or `ps` when unexplained
load remains after the runner obtains an exclusive lock.

## 4. Lock Order

Every invocation acquires locks in one order:

```text
1. admission.lock       exclusive, held for admission only
2. resource.lock        shared for normal, exclusive for heavy
3. admission.lock       released after resource admission
4. mirror-<hash>.lock   exclusive for the selected realpath
5. command              starts; --log opens at this point
```

A heavy waiter keeps `admission.lock` while current shared jobs drain.  New
normal jobs wait at step 1.  The common acquisition order prevents a cycle
between global and mirror locks.

## 5. Commands

Run a focused build from Git Bash:

```bash
MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu-24.04 -- \
  /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/run_resource_aware_task.sh \
  --workspace /home/peter/rh \
  --log /home/peter/rh/build-logs/endpoint-tail.log -- \
  /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Dev.C1CC20EndpointEigenvalueTail983 \
  ConnesWeilRH.Dev.C1CC20EndpointEigenvalueTail983Audit
```

Inspect a decision without taking a lock or running the command:

```bash
MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu-24.04 -- \
  /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/run_resource_aware_task.sh \
  --dry-run --workspace /home/peter/rh -- \
  /home/peter/.elan/bin/lake build ConnesWeilRH
```

Use `--class heavy` when domain knowledge shows that an unrecognized task can
fill the machine.  Use `--class normal` only for an opaque command whose CPU,
memory, and worker bounds you have inspected.  Static heavy rules and live
pressure can still upgrade that request.

The runner prints `RESOURCE_DECISION`, `RESOURCE_SNAPSHOT`, and one or more
`RESOURCE_REASON` lines before it waits.  With `--log`, the runner opens the
file after it owns both locks, so a queued invocation cannot truncate a log
that belongs to the active process.

## 6. Verification

Run the classifier and concurrency suite in WSL:

```bash
MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu-24.04 -- \
  /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/test_resource_aware_task.sh
```

The suite checks static classification, live-pressure escalation, normal
overlap on separate mirrors, same-mirror serialization, global heavy
exclusion, and heavy-waiter priority.  Lean acceptance still comes from the
build log: require the success footer and zero lines beginning with `error:`.
