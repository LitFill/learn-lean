open IO.FS

def bufsize : USize := 20 * 1024

-- #eval bufsize

partial
def dump (stream : Stream) : IO Unit
:= do
  let buf <- stream.read bufsize
  if buf.isEmpty
    then pure ()
  else
    (<- IO.getStdout).write buf
    dump stream

-- #check dump

def fileStream
  (fname : System.FilePath)
  : IO (Option Stream)
:= do
  if !(<- fname.pathExists) then
    (<- IO.getStderr).putStrLn
      s!"File not found {fname}"
    pure none
  else
    pure
      (some
      (Stream.ofHandle
      (<- Handle.mk fname Mode.read)))

def process
  (exitCode : UInt32)
  (args : List String)
  : IO UInt32
:= do
  match args with
  | [] => pure exitCode

  | "-" :: args =>
    dump (<- IO.getStdin)
    process exitCode args

  | fname :: args =>
    let stream <- fileStream ⟨fname⟩
    match stream with
    | none => process 1 args
    | some stream =>
        dump stream
        process exitCode args

def main (args : List String): IO UInt32 :=
  match args with
  | ["--help"] => do
    let usage :=
"Penggunaan: feline [PILIHAN]... [BERKAS]...
Concatenate FILE(s) to standard output.

Tanpa BERKAS, atau ketika BERKAS adalah -, baca masukan standar.
      --help        display this help and exit
      --version     output version information and exit

Contoh:
  feline f - g Keluarkan isi f, kemudian masukan standar, kemudian isi g.
  feline       Salin masukan standar ke keluaran standar."

    (<- IO.getStdout).putStrLn usage
    pure 0

  | ["--version"] => do
    (<- IO.getStdout).putStrLn "feline v0.1.0"
    pure 0

  | [] => process 0 ["-"]
  | _  => process 0 args

def Satu_tambah_satu_is_dua
  : Prop := 1 + 1 = 2

theorem satu_tambah_satu_is_dua
  :  Satu_tambah_satu_is_dua
  := rfl

-- set_option diagnostics true

theorem satu_tambah_satu_is_dua'
  :  1 + 1 = 2
  := by decide

theorem addAndAppend
  :  1 + 1 = 2 ∧ "Str".append "ing" = "String"
  := by decide

abbrev thefive := 2 + 3 = 5

theorem thefiveR : thefive := rfl

theorem thefiveD : thefive := by decide

def fifth
  (xs : List α)
  (ok : xs.length > 4)
  :  α
  := xs[4]

#eval fifth [1,3,5,7,9] (by decide)
