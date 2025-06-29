def main : IO Unit := do
  let stdin  <- IO.getStdin
  let stdout <- IO.getStdout

  stdout.putStrLn "What is your name?"

  let input <- stdin.getLine
  let name  := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def IO.myrepeat (action : IO Unit) : Nat -> IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    action.myrepeat n

/- #eval main.myrepeat 2 -/
/- #eval (IO.println "Hello").myrepeat 4 -/

def countdown : Nat -> List (IO Unit)
  | 0 => [IO.println "Boooooooom!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def List.runActions : List (IO Unit) -> IO Unit
  | [] => pure ()
  | a :: as => do { a ; as.runActions }

/- #eval (countdown 9).runActions -/
