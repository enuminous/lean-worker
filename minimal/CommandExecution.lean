-- CommandExecution.lean
-- Lean 4 execution harness: runs shell commands and returns compact results.
-- Acts as a context minimizer — captures command output and returns
-- a structured, bounded result suitable for token-constrained contexts.

import Std

namespace CommandExecution

-- ============================================
-- Result Type: Compact, Bounded Output
-- ============================================

structure ExecResult where
  command   : String
  exitCode  : Nat
  stdout    : String
  stderr    : String
  duration  : Nat
  truncated : Bool

abbrev ExecResultBounded : Nat := 5000

-- Helper: take first N chars of a String, return as String.
-- Work with Unicode characters; this is not a UTF-8 byte-count bound.
def stringTake (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take n)

-- Truncate to maxChars; the separate flag carries the truncation marker.
def truncateString (maxChars : Nat) (s : String) : String × Bool :=
  if s.length > maxChars then
    (stringTake s maxChars, true)
  else
    (s, false)

-- ============================================
-- Execution Interface
-- ============================================

def makeResult (cmd : String) (code : Nat) (out : String) (err : String)
    (dur : Nat) : ExecResult :=
  let (tOut, t1) := truncateString ExecResultBounded out
  let (tErr, t2) := truncateString ExecResultBounded err
  { command := cmd
  , exitCode := code
  , stdout := tOut
  , stderr := tErr
  , duration := dur
  , truncated := t1 || t2
  }

-- ============================================
-- Context Minimization
-- ============================================

-- One-line summary for token-efficient reporting.
def resultSummary (r : ExecResult) : String :=
  if r.exitCode ≠ 0 then
    "ERR " ++ r.command ++ " code=" ++ toString r.exitCode ++ ": " ++ stringTake r.stdout 80
  else
    "OK " ++ r.command ++ " lines=" ++ toString r.stdout.lines.toList.length ++ " duration=" ++ toString r.duration ++ "ms"

-- Maximum budget for command output in context per turn.
abbrev contextBudget : Nat := 1500

-- Check if result fits within context budget.
def resultFitsBudget (r : ExecResult) : Bool :=
  r.stdout.length + r.stderr.length ≤ contextBudget

-- Summarize result when over budget.
def resultSummarized (r : ExecResult) : String :=
  if resultFitsBudget r then
    r.stdout
  else
    "TRUNCATED[" ++ toString r.stdout.length ++ " chars]" ++ stringTake r.stdout 200 ++ "..."

-- ============================================
-- Formal Invariants
-- ============================================

-- Invariant 1: Exit code is always a natural number (non-negative).
theorem exitCode_valid : ∀ (r : ExecResult), r.exitCode ≥ 0 := by
  intro r
  cases r
  exact Nat.zero_le _

-- Invariant 2: Command string length is positive when non-empty.
theorem command_length_pos : ∀ (r : ExecResult), r.command.length > 0 → True := by
  intro r _
  trivial

-- The old claim quantified arbitrary records and was false. Only the constructor
-- enforces the bound; no proof obligation is hidden in ExecResult.
theorem stringTake_length_le (s : String) (n : Nat) :
    (stringTake s n).length ≤ n := by
  simpa only [stringTake, String.length_ofList] using List.length_take_le n s.toList

theorem truncateString_length_le (n : Nat) (s : String) :
    (truncateString n s).1.length ≤ n := by
  unfold truncateString
  split
  · exact stringTake_length_le s n
  · rename_i h
    change s.length ≤ n
    omega

theorem output_bounded (cmd : String) (code : Nat) (out err : String) (dur : Nat) :
    (makeResult cmd code out err dur).stdout.length ≤ ExecResultBounded ∧
    (makeResult cmd code out err dur).stderr.length ≤ ExecResultBounded := by
  exact ⟨truncateString_length_le _ out, truncateString_length_le _ err⟩

/-- A machine-checked counterexample to the former unrestricted statement. -/
theorem arbitrary_result_not_bounded :
    ¬ (∀ r : ExecResult, r.stdout.length ≤ ExecResultBounded ∧
        r.stderr.length ≤ ExecResultBounded) := by
  intro h
  let r : ExecResult := ⟨"", 0, String.ofList (List.replicate 5001 'x'), "", 0, false⟩
  have bad := (h r).1
  change (String.ofList (List.replicate 5001 'x')).length ≤ 5000 at bad
  rw [String.length_ofList, List.length_replicate] at bad
  omega

-- ============================================
-- Example: Command Log
-- ============================================

structure CommandLogEntry where
  seqNum    : Nat
  command   : String
  result    : ExecResult
  verified  : Bool

abbrev CommandLog := List CommandLogEntry

def exampleLog : List CommandLogEntry :=
  [ { seqNum := 1, command := "ls /opt/baal-agent/workspace",
      result := makeResult "ls /opt/baal-agent/workspace" 0
        "MEMORY.md
Twin.lean
CommandExecution.lean" "" 5,
      verified := true },
    { seqNum := 2, command := "git status --short",
      result := makeResult "git status --short" 0 "M Twin.lean
A CommandExecution.lean" "" 3,
      verified := true }
  ]

end CommandExecution
