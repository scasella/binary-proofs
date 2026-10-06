let cleanse_zero_memory_bytes_statement =
 `!p n. read (bytes(p:int64,n)) (\a:int64. word 0:byte) = 0`;;
let cleanse_read_bytes_zero_statement =
 `!m p n. read (bytes(p:int64,n)) m = 0 <=>
          !j. j<n ==> m(word_add p (word j)) = word 0`;;
let cleanse_prefix_zero_store_element_statement =
 `!m p i. read (bytes(p:int64,i)) m = 0
    ==> read (bytes(p,i+1))
          (write (element(word_add p (word i))) (word 0:byte) m) = 0`;;
let cleanse_prefix_zero_store_bytes8_statement =
 `!m p i. read (bytes(p:int64,i)) m = 0
    ==> read (bytes(p,i+1))
          (write (bytes8(word_add p (word i))) (word 0:byte) m) = 0`;;
let cleanse_state_prefix_zero_store_bytes8_statement =
 `!s p i. read (memory :> bytes(p:int64,i)) (s:x86state) = 0
    ==> read (memory :> bytes(p,i+1))
          (write (memory :> bytes8(word_add p (word i))) (word 0:byte) s) = 0`;;
