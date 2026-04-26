/- -------------------- -/
/- Using a Custom Monad -/
/- -------------------- -/

-- -----------------
-- Previous Stuff --
-- -----------------

def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

structure Config where
  useASCII      : Bool   := false
  currentPrefix : String := ""

def Config.preFile (cfg : Config) : String :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) : String :=
  if cfg.useASCII then "|  " else "│  "

-- change currentPrefix
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def configFromArgs : List String → Option Config
  | []          => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _           => none

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _           => pure ()
  | x :: xs, action => action x *> doList xs action

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

-- ---------------
-- Custom Monad --
-- ---------------

-- a reader is typically implemented as a function
-- ConfigIO is a function taking a Config, returning an IO (monad)
def ConfigIO (α : Type) : Type :=
  Config → IO α

-- it's basically a wrapper around the IO monad
instance : Monad ConfigIO where
  pure x           := fun _cfg => pure x              -- IO's pure
  bind result next := fun  cfg => do                  -- we are in the IO monad
                                  let v ← result cfg
                                  next v cfg

def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg

-- get/read current config
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg

-- overriding the current configuration
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action $ change cfg

-- IO -> ConfigIO (aka, turn IO into ConfigIO)
-- allows us to call IO actions from the standard library and turn it into a ConfigIO
def runIO (action : IO α) : ConfigIO α :=
  fun _cfg => action -- just ignore the configuration

-- takes configuration implicitly through the ConfigIO monad
def showFileName (file : String) : ConfigIO Unit := do
  runIO $ IO.println $ (← currentConfig).fileName file

-- takes configuration implicitly through the ConfigIO monad
def showDirName (dir : String) : ConfigIO Unit := do
  runIO $ IO.println $ (← currentConfig).dirName dir

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do -- we are in the ConfigIO monad
  match ← runIO $ toEntry path with
    | none              => pure () -- ConfigIO's pure
    | some $ .file name => showFileName name
    | some $ .dir  name => showDirName  name
                           let contents ← runIO path.readDir
                           locally (·.inDirectory)
                                   (doList (contents.qsort dirLT).toList
                                           fun dir => dirTree dir.path)

def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config => (dirTree $ ← IO.currentDir).run config
                     pure 0
    | none        => IO.eprintln s!"Didn't understand argument(s) {" ".intercalate args}\n"
                     IO.eprintln usage
                     pure 1
