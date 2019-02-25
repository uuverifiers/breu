package breu;

import org.scalatest.FunSuite
import org.scalatest._
import java.io.File
import scala.io.Source

class Online extends FunSpec {

  describe("LazyOnlineSolver") {

    it("Term creation/deletion") {
      val a = "a"
      val b = "b"
      val c = "c"
      val d = "d"
      val e = "e"
      val f = "f"

      val X = "X"
      val Y = "Y"
      val Z = "Z"

      val solver = new Solver[String, String]()

      // println("\t\t ADDING a,b,c, and X")
      solver.addConstants(a, b, c)
      solver.addVariable(X, Set(a,b,c))
      solver.addGoal(List((X, X)))
      solver.push()

      // println("\t\t ADDING Y")
      solver.addVariable(Y, Set(a,b,c, X))
      solver.addGoal(List((Y, Y)))      
      solver.push()

      assert(solver.solve() == breu.Result.SAT)

      // println("\t\t DELETING Y")
      solver.pop()

      assert(solver.solve() == breu.Result.SAT)

      // println("\t\t ADDING Z")
      solver.addVariable(Z, Set(a,b,c,X))
      solver.addGoal(List((Z, Z)))
      solver.push()
      assert(solver.solve() == breu.Result.SAT)

      // println("\t\t ADDING Y")
      solver.addVariable(Y, Set(a,b,c,X,Z))
      solver.addGoal(List((Y, Y)))
      solver.push()
      assert(solver.solve() == breu.Result.SAT)

      // println("\t\t DELETING Y and Z")
      solver.pop()
      solver.pop()
      assert(solver.solve() == breu.Result.SAT)
    }

    it("multipleGoals") {
      val c0 = "c0"      
      val c1 = "c1"
      val c2 = "c2"
      val x3 = "x3"

      val solver = new Solver[String, String]()

      solver.addConstants(c0, c1, c2)
      solver.addVariable(x3, Set(c0, c1, c2, x3))

      solver.addGoal(List((c0, x3), (c2, x3)))
      solver.addGoal(List((c0, c0), (c2, c1)))
      solver.addGoal(List((c0, c1), (c2, c2)))
      solver.addGoal(List((x3, c0), (x3, c2)))
      solver.addGoal(List((c0, c0), (c1, c2)))
      solver.addGoal(List((c1, c0), (c2, c2)))                           
      solver.push()

      assert(solver.solve() == breu.Result.UNSAT)
    }


    it("DisunificationConstraint") {
      val a = "a"
      val b = "b"
      val c = "c"
      val d = "d"

      val X = "X"
      val Y = "Y"
      val Z = "Z"

      val solver = new Solver[String, String]()      

      def base() = {
        solver.addVariable(a, Set(a))
        solver.addVariable(b, Set(b))
        solver.addVariable(c, Set(c))
        solver.addVariable(X, Set(X, a,b, c))
        solver.addVariable(Y, Set(Y, X, a, b, c))
        solver.addGoal(List((X,a), (Y, b)))
      }

      base()
      solver.push()
      assert(solver.solve() == breu.Result.SAT)
      solver.pop()

      base()
      solver.addDisunificationConstraint(List((X, a), (c,c)))
      solver.addDisunificationConstraint(List((X, Y), (a, c)))      
      solver.push()
      assert(solver.solve() == breu.Result.UNSAT)            
    }
  }
}
