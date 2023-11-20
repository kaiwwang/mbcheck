open Common.Ir

type process = program * pid * steps * comp * environment * frame_stack 
and pid = int
and steps = int
and environment = (Common.Ir.Binder.t * Common.Ir.value) list
and frame = Frame of Binder.t * environment * comp
and frame_stack = frame list


type execution_status =
  | Finished
  | Unfinished
  | Spawned of process 
  | MessageToSend of value * message
  | Blocked of RuntimeName.t
  | FreeMailbox of RuntimeName.t


