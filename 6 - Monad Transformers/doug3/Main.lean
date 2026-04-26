/- ---------------------------- -/
/- Adding a Reader to Any Monad -/
/- ---------------------------- -/

-- -----------------
-- Previous Stuff --
-- -----------------

structure Config where
  useASCII      : Bool   := false
  currentPrefix : String := ""

def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs : List String → Option Config
  | []          => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _           => none

inductive Entry where
  | file : String → Entry
  | dir  : String → Entry
deriving Repr

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none                 => pure $ some $ .dir "" -- should never happen
  | some "." | some ".." => pure none
  | some name            => pure $ some (if (← path.isDir)
                                           then .dir name
                                           else .file name)

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _           => pure ()
  | x :: xs, action => action x *> doList xs action

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def Config.preFile (cfg : Config) : String :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) : String :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

-- --------------------
-- Monad Transformer --
-- --------------------

-- A monad transformer takes a monad as an argument and returns a new monad.
-- Monad transformers consist of:
--  · A definition of the transformer itself, which is typically a function from types to types
--  · A Monad instance that assumes the inner type is already a monad
--  · An operator to "lift" an action from the inner monad to the transformed monad, akin to runIO
    
-- NOTE: This is the main change from doug2!
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none              => pure ()
    | some $ .file name => showFileName name
    | some $ .dir name  => showDirName  name
                           let contents ← path.readDir
                           withReader (·.inDirectory)
                                      (doList (contents.qsort dirLT).toList
                                              fun d => dirTree d.path)

def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config => (dirTree (← IO.currentDir)).run config
                     pure 0
    | none        => IO.eprintln s!"Didn't understand argument(s) {" ".intercalate args}\n"
                     IO.eprintln usage
                     pure 1
