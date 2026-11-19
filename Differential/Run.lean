import ZellicX86.Spec.Step
import ZellicX86.Spec.MemoryEval
import ZellicX86.Spec.Linux.Exec
/-!
# Concrete calls of a function in the model

A processor, an environment that does nothing (`quiet`), and the entry state of a call `f(rdi, rsi, rdx)` of code
placed at `entry`, with one object mapped readable and writable, so that two functions' code can be run from the same
call and their results compared.
-/
namespace Differential
open ZellicX86

deriving instance Inhabited for AuxCpu, CpuidResult, Vendor, LinuxBoot, Profile

/-- An x86-64-v4 processor (AVX-512F/VL/BW/DQ, AVX2, BMI1/2, LZCNT, RTM), one CPU, the kernel having enabled the
x87, SSE, AVX and AVX-512 state in `XCR0`. -/
def prof : Profile :=
  { (default : Profile) with
    feat := { (default : Features) with
      ssse3 := true, sse3 := true, sse41 := true, sse42 := true, avx := true, avx2 := true, fma := true,
      bmi1 := true, bmi2 := true, lzcnt := true, movbe := true, nx := true, rtm := true,
      avx512f := true, avx512vl := true, avx512bw := true, avx512dq := true }
    cpus := 1
    xcr0 := some 0xe7
    mxcsrMask := 0xffff }

/-- `EIO`, the answer the environment gives below to requests that can fail. -/
def eio : Errno := ⟨5, by decide⟩

deriving instance Inhabited for FileAttrs, Timespec, Files, Rlimit, FilePos

/-- `0 < max cpus 1`. -/
theorem one {cpus : Nat} : (0 : BitVec 32).toNat < max cpus 1 :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)

/-- An environment that does nothing between instructions (`between` answers `[]`: `quiet_undisturbed`), leaves
undefined values 0, takes the first alternative, and fails every request a system call would make. -/
def quiet : Oracle := fun _ r => match r with
  | .undefined w => (0 : BitVec w)
  | .pick n => (0 : Fin (n + 1))
  | .between _ => ⟨[], nofun⟩
  | .read .. => .error eio
  | .readFail .. => none
  | .write .. => .error eio
  | .writeRefused _ => some eio
  | .writeFault .. => .error eio
  | .fileAttrs _ => (default : FileAttrs)
  | .place _ => (0 : BitVec 64)
  | .memFail _ => some (eio, 0)
  | .growFail _ => true
  | .hugeFail _ => true
  | .dataLimitIgnored => false
  | .tsc => (0 : BitVec 64)
  | .xinuse required => ⟨required, BitVec.and_self⟩
  | .randomCount _ => .error eio
  | .randomBytes k => ⟨List.replicate k 0, List.length_replicate⟩
  | .readlink .. => .error eio
  | .stat _ => .error eio
  | .openAt .. => .error eio
  | .seekPast .. => false
  | .seek .. => .error eio
  | .ioctlGet .. => .error eio
  | .close _ => none
  | .fdGrow _ => .error eio
  | .fcntl .. => some eio
  | .positional .. => false
  | .resumeIds _ => ⟨(0, 0, 0), by simp only [EnvEvent.OnCpus]; exact ⟨one, one⟩⟩
  | .setRlimit .. => some eio
  | .queued _ => false
  | .initPkru => ⟨0, rfl⟩
  | .clock _ => (default : Timespec)
  | .rtcAlarm => false
  | .timezone => (0 : BitVec 64)
  | .cpuNode _ => ⟨(0, 0), one⟩

/-- A page mapped with protection `prot`, backed by backing number `p`. -/
def page (prot : Prot) (p : PageNum) : Option Mapping :=
  some { prot, backing := p.toNat, pkey := 0, special := false, origin := none, area := p.toNat,
         maxProt := ⟨true, true, true⟩, growsDown := false, huge := none }

/-- Where the code is placed (`entry`), the return address (`ra`, unmapped: the caller is not modelled) and the stack's
top: `rsp` at entry points at the return address, `rsp + 8` a multiple of 16 (`sysv`). -/
def entry : Addr := 0x401000
def ra : Addr := 0x7ffff0000000
def rsp : Addr := 0x7fffffffe008

/-- The page of each part of the address space: the code (`entry`'s page, 1 page: every variant is under 4096 bytes),
the stack (`rsp`'s page) and the object's pages. -/
def codePage : Nat := entry.toNat / 4096
def stackPage : Nat := rsp.toNat / 4096

/-- A call's input: the object's pages (`objPages` pages from page `objPage`, mapped read and write, apart from the code
and the stack pages), their bytes `obj`, and the arguments `s`, `c`, `n` (`rdi`, `rsi`, `rdx`). -/
structure Input where
  objPage : Nat
  objPages : Nat
  obj : Addr → Byte
  s : Addr
  c : Addr
  n : Addr

/-- The memory of a call: the code `code` at `entry` (read and execute), the stack page with the return address at
`rsp` (read and write), and the input's object pages. -/
def memory (code : List Byte) (i : Input) : Memory :=
  let cover := [(codePage, 1), (stackPage, 1), (i.objPage, i.objPages)]
  { map := mapOn cover fun p =>
      if p.toNat = codePage then page ⟨true, false, true⟩ p else page ⟨true, true, false⟩ p
    backings := fun b => .priv fun o =>
      let a : Addr := BitVec.ofNat 64 (4096 * b + o.toNat)
      if b = codePage then code.getD o.toNat 0
      else if b = stackPage then
        (if rsp ≤ a ∧ a < rsp + 8 then (ra >>> (8 * (a - rsp).toNat)).setWidth 8 else 0)
      else i.obj a
    files := default
    growsDown := []
    fresh := 2 ^ 52
    cover
    covers := mapOn_covers }

/-- The entry state of the call `f(s, c, n)` of the code `code` at `entry` on input `i`. -/
def call (code : List Byte) (i : Input) : State :=
  let cpu := entryCpu entry.toNat rsp.toNat 0
  { proc := { mm := { mem := memory code i, brkMin := 0x1000, brk := 0x1000, startBrk := 0x1000, startData := 0,
                      endData := 0 }
              files := fun _ => none
              opens := { pos := fun _ => default, next := 0 }
              sighand := fun _ => SigAction.dfl
              signal := { pending := [], rlimits := fun _ => default, unkillable := false }
              fdMax := 1024 }
    cpu := { cpu with gpr := { cpu.gpr with rdi := i.s, rsi := i.c, rdx := i.n } }
    thread := { tid := 1, sigmask := 0, pending := [], altStack := AltStack.disabled, rseq := none,
                clearChildTid := 0, robustList := 0, cpuidFaults := false, tscFaults := false, shstk := none,
                uid := 0 } }

/-- Steps from `s` until `rip` is `ra`, at most `fuel` of them: the first state at `ra` and the number of steps taken,
or `none` if the run ends or does not get there within `fuel` steps. -/
def toReturn (prof : Profile) (o : Oracle) (ra : Addr) : Nat → State → Nat → Option (State × Nat)
  | 0, _, _ => none
  | fuel + 1, s, t =>
    match (step prof s).runStream o t with
    | (.running s' _, t') =>
      if s'.cpu.rip = ra then some (s', 1) else (toReturn prof o ra fuel s' t').map fun (x, k) => (x, k + 1)
    | (.stopped _, _) => none

/-- `rax` at the first return of the call of `code` on input `i`, and the steps taken, within `fuel` steps. -/
def retRax (fuel : Nat) (code : List Byte) (i : Input) : Option (Addr × Nat) :=
  (toReturn prof quiet ra fuel (call code i) 0).map fun (x, k) => (x.cpu.gpr.rax, k)

end Differential
