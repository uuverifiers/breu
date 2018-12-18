package breu

import scala.collection.mutable.{Map => MMap, ListBuffer, Queue}

class Disequalities(
  val size : Int,
  val eqsAux : Array[Eq],
  val timeoutChecker : () => Unit) {

  def this(that : Disequalities) {
    this(that.size, Array(), that.timeoutChecker)
    eqArgs ++= that.eqArgs
    eqRes ++= that.eqRes
    eqEqs ++= that.eqEqs
    eqEqs = that.eqEqs
    // DQmap ++= that.DQmap
  }

  override def toString = {
    "<---Disequality--->" + "\n" +
    (for ((k, v) <- DQmap) yield {
      k + " = " + v
    }).mkString(", ") + "\n" + 
    "eqArgs: " + eqArgs.size + "\n" +
    "eqRes: " + eqRes.size + "\n" +
    "eqEqs: " + eqEqs.size + "\n" +
    "eqEqs: " + eqEqs.size + "\n"
  }

  // TODO: Fix!
  var eqEqs = eqsAux

  // Stores the actual disequalities 
  // TODO: change to (size*size-1)/2
  val DQmap = MMap() : MMap[(Int, Int), Int]

  // Buffer to store change to allow backtracking (old, s, t)
  var changes = ListBuffer() : ListBuffer[(Int, Int, Int)]

  // Maps terms to eqEqs with t in argument 
  // | Term -> List(Eqction, Index, eqEq)
  var eqArgs = MMap() : MMap[Int, ListBuffer[(Int, Int, Int)]]

  // Maps terms to eqEqs with t in result
  // | Term -> List(Eqction, eqEq)
  var eqRes = MMap() : MMap[Int, ListBuffer[(Int, Int)]]

  // Eq -> List[eqctions]
  // Maps eqction symbols to eqEqs with given eqction symbol 
  // | Eqction -> List(eqEqs)
  var eqFuns = MMap() : MMap[Int, ListBuffer[Int]]

  // if (DQ(i)(j) == 0)
  //   diseqCount += 1

  for (f <- 0 until eqEqs.length) {
    val (fun, args, res) = (eqEqs(f).fun, eqEqs(f).args, eqEqs(f).res)

    // Argument map
    for (i <- 0 until args.length) {
      if (eqArgs contains (args(i)))
        eqArgs.get(args(i)).get += ((fun, i, f))
      else
        eqArgs += (args(i) -> ListBuffer((fun, i, f)))
      () // This is needed for bug
    }

    // Result map
    if (eqRes contains(res))
      eqRes.get(res).get += ((fun, f))
    else
      eqRes += (res -> ListBuffer((fun, f)))

    // Function symbol map
    if (eqFuns contains(fun))
      eqFuns.get(fun).get += f
    else
      eqFuns += (fun -> ListBuffer(f))
    () // This is needed for bug
  }

  // TODO: diseqCount
  // var diseqCount = 0

  def doprint : Unit = {
    println("DQ:")
    for (i <- 0 until size) {
      for (j <- 0 until size) {
        print(" " + getDQ(i, j))
      }
      println("")
    }
  }

  def getDQ(i : Int, j : Int) = {
    val (x, y) = (i min j, i max j)
    DQmap getOrElse ((x, y), 0)
  }

  def setDQ(i : Int, j : Int, v : Int) = {
    val (x, y) = (i min j, i max j)
    DQmap += (x, y) -> v
  }
 
  def apply(i : Int, j : Int) : Boolean = getDQ(i, j) != 0

  def getFunified(t : Int) = {
    for (s <- 0 until size; if getDQ(s, t) >= 1) yield s
  }

  def getINEQ() = {
    (for (i <- 0 until size; j <- 0 until size;
      if (i < j); if (0 == getDQ(i, j))) yield
      (i,j))
  }

  def inequalities(terms : Seq[Int]) = {
    (for (i <- terms; j <- terms;
      if (i < j); if (!this(i, j))) yield
      (i,j))
  }

  def update(i : Int, j : Int, v : Int) = {
    val ii = i min j
    val jj = i max j

    val old = getDQ(ii, jj)
    changes += ((old, ii, jj))

    setDQ(ii, jj, v)
  }

  def unify(i : Int, j : Int) = {
    if (getDQ(i, j) < 1) {
      // diseqCount -= 1
      update(i, j, 1)
    }
  }

  def funify(i : Int, j : Int) = {
    if (getDQ(i ,j) < 2) {
      // if (dq(i,j) < 1)
      //   diseqCount -= 1
      update(i, j, 2)
    }
  }

  def check(pairs : Seq[(Int, Int)]) : Boolean = {
    var primitiveCheck = true
    for ((s, t) <- pairs; if !this(s,t))
      primitiveCheck = false
    primitiveCheck

    // var advancedCheck = true

    // if (pairs.isEmpty) {
    //   // true
    // } else {
    //   // var equal = true

    //   val uf = new UnionFind[Int]

    //   for ((s, t) <- pairs) {
    //     if (!(uf contains s))
    //       uf.makeSet(s)
    //     if (!(uf contains t))
    //       uf.makeSet(t)

    //     if (!this(s, t))
    //       advancedCheck = false
    //     else
    //       uf.union(s,t)
    //   }


    //   if (advancedCheck) {
    //     for (set <- uf.getSets) {
    //       if (set.size > 2) {
    //         // println("check(" + pairs + ")")
    //         // println("\t" + uf)
    //         // println("\t" + uf.getSets)

    //         for (s <- set; t <- set; if s < t) {
    //           if (!this(s,t)) {
    //             advancedCheck = false
    //             // println("\t\tChecking " + s + " != " + t)
    //             // throw new Exception("Transitivity CHECK!")
    //           }
    //         }
    //       }
    //     }
    //   }
    //   // equal
    // }

    // if (advancedCheck != primitiveCheck) {
    //   println("advancedCheck != primitiveCheck!")
    // } 
    // advancedCheck
  }


  def funUnify(s : Int, t : Int) : Set[(Int, Int)] = {
    val sEq =
      for (i <- 0 until size; if (this(s, i))) yield i
    val tEq =
      for (i <- 0 until size; if (this(t, i))) yield i

    (for (i <- sEq; j <- tEq; if i != j; if !this(i,j)) yield {
      (i min j, i max j)
    }).toSet
  }

  def remove(s : Int, t : Int) = {
    setDQ(s, t, 1)
  }

  def cascadeRemove(s : Int, t : Int) : Unit = Timer.measure("cascadeRemove") {
    // Timer.measure("cascadeRemove") {
    val todo = Queue() : Queue[(Int, Int)]
    val inQueue = Array.ofDim[Boolean](size, size)

    def addTodo(newEq : (Int, Int), fun : Boolean) = Timer.measure("addTodo") {
      val (ss, tt) = newEq
      val s = ss min tt
      val t = ss max tt
      val curdq = getDQ(s, t)

      val queue = 
        if (fun && curdq < 2) {
          funify(s, t)
          true
        } else if (curdq < 1) {
          unify(s, t)
          true
        } else {
          false
        }

      if (queue && !inQueue(s)(t)) {
        // println("\tAdding " + ((s, t)))
        inQueue(s)(t) = true
        todo.enqueue((s, t))
      }
    }

    // Add initial todo item
    addTodo((s, t), false)

    while (!todo.isEmpty) {
      timeoutChecker()
      val (s, t) = todo.dequeue
      inQueue(s)(t) = false

      // TODO: ASSERT
      if (!this(s, t))
        throw new Exception("Tuple " + ((s,t)) + " in todo not unified!")


      // Functionality
      for ((fun1, i1, eq1) <- eqArgs.getOrElse(s, List()); 
        (fun2, i2, eq2) <- eqArgs.getOrElse(t, List()); 
        if (fun1 == fun2 && i1 == i2 && eq1 != eq2)) yield {

        val (args_i, r_i) = (eqEqs(eq1).args, eqEqs(eq1).res)
        val (args_j, r_j) = (eqEqs(eq2).args, eqEqs(eq2).res)

        if (check(args_i zip args_j)) {
          addTodo((r_i, r_j), true)
          for (eq <- funUnify(r_i, r_j))
            addTodo(eq, false)
        }
      }

      // Find all s, s.t. s = lhs and add s = rhs
      def transitivity(lhs : Int, rhs : Int) = Timer.measure("transitivity") {
        for ((fun1, eq1) <- eqRes getOrElse (lhs, List())) {
          val args_i = eqEqs(eq1).args

          // Find all matching equations
          for (eq2 <- eqFuns getOrElse (fun1, List())) {
            val (args_j, s) = (eqEqs(eq2).args, eqEqs(eq2).res)

            // s = lhs => s = rhs
            // Unify s with all terms that are Funified with rhs
            if (check(args_i zip args_j))
              for (funified <- getFunified(s))
                addTodo((rhs, funified), false)
          }
        }
      }


      // Timer.measure("cascadeRemove.transitivity") {
      transitivity(s, t)
      transitivity(t, s)
      // }
    }
  }

  def minimise(
    terms : Seq[Int],
    goals : Seq[Seq[(Int, Int)]], 
    heuristic : (((Int, Int)) => Int)) = {
    // Go through all disequalities
    // We try to remove disequalities one by one
    // TODO: make it smarter
    this.setBase
    val ineqs = inequalities(terms)
    val ineqsSort = ineqs.sortBy(x => heuristic(x)).reverse

    for ((s, t) <- ineqsSort) {
      timeoutChecker()
      this.cascadeRemove(s, t)
      val sat = this.satisfies(goals)
      if (!sat) {
        this.setBase
      } else {
        this.restore
      }
    }

    assert(!this.satisfies(goals))
  }

  def setBase = changes = ListBuffer()

  def restore = {
    for ((old, s, t) <- changes.reverse) {
      // if (old == 0)
      //   diseqCount += 1
      setDQ(s, t, old)
    }

    changes = ListBuffer()
  }

  def satisfies(goals : Seq[Seq[(Int, Int)]]) = {
    var satisfiable = false

    // println("SATISFIES?")
    // println("GOALS: " + goals.mkString(" OR "))
    // println(this.getINEQ().mkString("; "))

    for (subGoal <- goals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (!this(s,t))
          allPairsTrue = false

        if (!allPairsTrue)
          subGoalSat = false

      }
      if (subGoalSat)
        satisfiable = true
    }
    satisfiable
  }
}
