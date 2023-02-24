/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

namespace Mathport

@[extern "lean_set_max_heartbeat"]
opaque setMaxHeartbeat (max : USize) : BaseIO Unit

@[extern "lean_reset_heartbeat"]
opaque resetHeartbeat : BaseIO Unit

def withMaxHeartbeat [Monad m] [MonadFinally m] [MonadLiftT BaseIO m]
    (max : USize) (k : m α) : m α := do
  resetHeartbeat
  setMaxHeartbeat max
  try
    k
  finally
    setMaxHeartbeat 0

@[noinline]
private unsafe def withMaxHeartbeatPureImpl (max : USize) (k : {_ : Unit} → α) : α :=
  unsafeBaseIO do withMaxHeartbeat max do return @k (← pure ())

@[implemented_by withMaxHeartbeatPureImpl]
opaque withMaxHeartbeatPure {α : Type} (max : USize) (k : {_ : Unit} → α) : α :=
  @k ()
