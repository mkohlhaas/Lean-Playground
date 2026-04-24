/- ======================== -/
/- The Applicative Contract -/
/- ======================== -/

/- ----------------------------- -/
/- All Applicatives are Functors -/
/- ----------------------------- -/

-- One can construct a Functor instance from an Applicative instance.
-- Given an Applicative one can construct a Functor.

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

class MyApplicative (f : Type → Type) extends Functor f where
  pure    : α → f α
  seq   : f (α → β) → (Unit → f α) → f β
  map g x     := seq (pure g) (fun () => x)     -- default implementation for `map` in terms of `seq` and `pure`

#print Functor    
#print Applicative

/- ----------------------------------- -/
/- All Monads are Applicative Functors -/
/- ----------------------------------- -/

-- One can construct an Applicative instance from a Monad instance.
-- Given a Monad one can construct an Applicative.

-- implementation for `seq` in terms of `bind` and `pure`
def seq' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure $ g y
  
-- the same with bind's infix operator (>>=)
def seq'' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f    >>= fun g =>
  x () >>= fun y =>
  pure $ g y

class MyMonad (m : Type → Type) extends Applicative m where
  bind :  m α → (α → m β) → m β
  seq f x    := bind f      fun g =>            -- default implementation for `seq` in terms of `bind` and `pure`
                bind (x ()) fun y =>
                pure $ g y

-- NOTE: Every Monad instance automatically generates Applicative and Functor instances!

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

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs  -- NOTE: only reports first error! (see below)
  | .ok x        => next x

instance : Functor (Validate ε) where
  map f
  | .ok x        => .ok $ f x
  | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure    := .ok
  seq f x := match f with
             | .ok g        => g <$> x ()
             | .errors errs =>
               match x () with
               | .ok _         => .errors errs
               | .errors errs' => .errors (errs ++ errs')

def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }

deriving instance Repr, BEq for NonEmptyList, Validate

-- Combined implementations of Functor, Applicative and Monad should work equivalently to these default implementations.
-- In other words, a type that provides both Applicative and Monad instances should not have an implementation of seq that works differently from the version that the Monad instance generates as a default implementation.
-- This is important because polymorphic functions may be refactored to replace a use of >>= with an equivalent use of <*>, or a use of <*> with an equivalent use of >>=.
-- This refactoring should not change the meaning of programs that use this code.

-- This rule explains why Validate.andThen should not be used to implement bind in a Monad instance.
#eval notFun <*> notArg                                                              
#eval notFun.andThen fun f => notArg.andThen fun x => pure $ f x                     
#eval notFun <*> notArg == notFun.andThen fun g => notArg.andThen fun y => pure (g y)
