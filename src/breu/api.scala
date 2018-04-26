package breu;

import scala.collection.mutable.ListBuffer


object api {

  var i = 0

  def reset() {
    i = 0
  }

  def inc() = {
    i += 1
  }

  def print() = {
    println("i: " + i)
  }
}
