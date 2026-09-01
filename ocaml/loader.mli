exception Malformed of int64 * string

val load : string ->
  Uint63.t *
  (Uint63.t *
   (((Z.t Native_array.t * Z.t) Native_array.t) *
    (((Uint63.t Native_array.t *
       (((Z.t Native_array.t * Z.t) *
         (Uint63.t Native_array.t * Uint63.t Native_array.t)))) Native_array.t) *
     (((Uint63.t Native_array.t Native_array.t) *
       ((Uint63.t Native_array.t * Uint63.t) Native_array.t)) *
      (((Uint63.t Native_array.t Native_array.t) *
        ((Uint63.t Native_array.t Native_array.t) *
         (Uint63.t Native_array.t Native_array.t))) *
       ((((Z.t Native_array.t * Z.t) *
          ((Z.t Native_array.t Native_array.t) * (Z.t Native_array.t Native_array.t)))) *
        ((Uint63.t *
          ((Uint63.t Native_array.t) *
           ((Z.t Native_array.t Native_array.t) *
            ((Z.t Native_array.t Native_array.t) *
             ((Uint63.t * Z.t) Native_array.t Native_array.t))))))))))))
