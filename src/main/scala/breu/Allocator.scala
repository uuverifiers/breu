package breu

//
//  Allocates bits for the solver
//
class Allocator {
  // Leave room for ONEBIT (1) and ZEROBIT (2)
  var next = 3

  def reset = {
    next = 3
  }

  def alloc(count : Int) = {
    val ret = next
    next = next + count
    ret
  }
}
