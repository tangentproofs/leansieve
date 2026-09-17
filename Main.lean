import RakeSieve


def main : IO Unit := do
  let mut s : PrimeSieve _ := { state := RakeSieve.init }
  let mut r : List NPrime := []
  for _ in [0:5] do
    r := s.state.p :: r
    s := s.next
  IO.println <| r.reverse

#eval! main
