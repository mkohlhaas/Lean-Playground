/- ======================== -/
/- The Applicative Contract -/
/- ======================== -/

/- ----------------------------- -/
/- All Applicatives are Functors -/
/- ----------------------------- -/

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

class MyApplicative (f : Type → Type) extends Functor f where
  pure    : α → f α
  seq     : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)

/- ----------------------------------- -/
/- All Monads are Applicative Functors -/
/- ----------------------------------- -/

def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)

def seq' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f    >>= fun g =>
  x () >>= fun y =>
  pure (g y)

class MyMonad (m : Type → Type) extends Applicative m where
  bind    : m α → (α → m β) → m β
  seq f x := bind f      fun g =>
             bind (x ()) fun y =>
             pure (g y)

/- ----------------------- -/
/- Additional Stipulations -/
/- ----------------------- -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

inductive Validate (ε α : Type) : Type where
  | ok     : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
  | .ok x        => .ok (f x)
  | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure    := .ok
  seq f x := match f with
             | .ok g        => g <$> (x ())
             | .errors errs =>
               match x () with
               | .ok _         => .errors errs
               | .errors errs' => .errors (errs ++ errs')

def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
