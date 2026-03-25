import Greeting
import Greeting.Smile

-- The module name hierarchy is decoupled from the namespace hierarchy.
-- In Lean, modules are units of code distribution, while namespaces are units of code organization.
-- That is, names defined in the module Greeting.Smile are not automatically in a corresponding namespace Greeting.Smile.
-- In particular, happy is in the Expression namespace.
-- Modules may place names into any namespace they like, and the code that imports them may open the namespace or not.
-- import is used to make the contents of a source file available, while open makes names from a namespace available in the current context without prefixes.

/- open Expression -/
open Expression (happy)

def main : IO Unit :=
  IO.println s!"Hello, {hello} with {happy}!!"
