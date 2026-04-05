-- from previous chapters

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

/- -------------------------------- -/
/- Constructor Syntax for Instances -/
/- -------------------------------- -/

structure Tree : Type where
  latinName   : String
  commonNames : List String

-- useful when emphasizing that a structure type is tuple alike
def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

-- idiomatic
def birch : Tree :=
  { latinName   := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

-- idiomatic
def sloe : Tree where
  latinName   := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

-- Behind the scenes, type classes are structure types and instances are values of these types.

-- same syntaxes allowed
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

-- idiomatic
instance : Display Tree where
  displayName t := t.latinName

/- -------- -/
/- Examples -/
/- -------- -/

-- An example is like a definition without a name.

-- In source files, example declarations are best paired with comments that
-- explain how the example illustrates the concepts of the library.

example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }

-- function example, but cannot be called
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
