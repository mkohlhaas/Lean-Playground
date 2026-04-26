export MonadReader (read)
export MonadWithReader (withReader)

def MyReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

#print ReaderT

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

def read [Monad m] : ReaderT ρ m ρ := fun env => pure env

#print MonadReader

instance [Monad m] : Monad (ReaderT ρ m) where
  pure x           := fun _ => pure x
  bind result next := fun env => do
                                  let v ← result env
                                  next v env

class MyMonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α

#print MonadLift

instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action

class MyMonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α

#print MonadWithReader

instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action := fun cfg => action (change cfg)
