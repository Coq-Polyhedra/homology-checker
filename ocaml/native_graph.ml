let bfs
    (graph : Uint63.t Native_array.t Native_array.t)
    (start : Uint63.t) : Uint63.t =
  let vertices = graph.Native_array.data in
  let vertex_count = Array.length vertices in
  let start = Native_array.int_of_uint63 start in

  if start < 0 || start >= vertex_count then
    Native_array.uint63_of_int 0
  else begin
    let visited = Bytes.make vertex_count '\000' in

    (* Every vertex is inserted at most once, so a queue of size |V|
       is sufficient. *)
    let queue = Array.make vertex_count 0 in
    let head = ref 0 in
    let tail = ref 1 in
    let visited_count = ref 1 in
    let valid = ref true in

    Bytes.unsafe_set visited start '\001';
    Array.unsafe_set queue 0 start;

    while !valid && !head < !tail do
      let vertex = Array.unsafe_get queue !head in
      incr head;

      let neighbours =
        (Array.unsafe_get vertices vertex).Native_array.data
      in

      for i = 0 to Array.length neighbours - 1 do
        if !valid then begin
          let neighbour =
            Native_array.int_of_uint63
              (Array.unsafe_get neighbours i)
          in

          if neighbour < 0 || neighbour >= vertex_count then
            valid := false
          else if Bytes.unsafe_get visited neighbour = '\000' then begin
            Bytes.unsafe_set visited neighbour '\001';
            Array.unsafe_set queue !tail neighbour;
            incr tail;
            incr visited_count
          end
        end
      done
    done;

    if !valid then
      Native_array.uint63_of_int !visited_count
    else
      Native_array.uint63_of_int 0
  end