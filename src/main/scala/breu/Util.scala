package breu;

import scala.collection.mutable.{Set => MSet, HashMap => MHashMap}


class UnionFind[D] {
  private val parent = new MHashMap[D, D]
  private val rank   = new MHashMap[D, Int]

  def apply(d : D) : D = {
    val p = parent(d)
    if (p == d) {
      p
    } else {
      val res = apply(p)
      parent.put(d, res)
      res
    }
  }

  def makeSet(d : D) : Unit = {
    parent.put(d, d)
    rank.put(d, 0)
  }

  def union(d : D, e : D) : Unit = {
    val dp = apply(d)
    val ep = apply(e)
    
    if (dp != ep) {
      val dr = rank(dp)
      val er = rank(ep)
      if (dr < er) {
        parent.put(dp, ep)
      } else if (dr > er) {
        parent.put(ep, dp)
      } else {
        parent.put(ep, dp)
        rank.put(dp, dr + 1)
      }
    }
  }

  def getSets = parent.groupBy(_._2).mapValues(_.map(_._1)).values

  def contains(d : D) : Boolean = {
    parent contains d
  }

  override def toString : String = parent.toString
}

object Util {
  // Calculating log_2 (b)
  // Used for cacluating number of bits needed
  def binlog(b : Int) : Int = {
    var bits = b
    var log = 0
    if ((bits & 0xffff0000) != 0) {
      bits >>>= 16
      log = 16
    }
    
    if (bits >= 256) {
      bits >>>= 8
      log += 8
    }
    if (bits >= 16) {
      bits >>>= 4
      log += 4
    }
    
    if (bits >= 4) {
      bits >>>= 2
      log += 2
    }

    // TODO: Add 1 for luck!
    // Add one if we have an even power of 2
    // if ((b & (b -1)) == 0)
    return log + ( bits >>> 1 ) + 1
    // else
    // return log + (bits >>> 1)
  }

  def BreunionFind(
    terms : Seq[Int],
    eqs : Seq[Eq],
    assignments : Seq[(Int, Int)] = List()) 
  : UnionFind[Int]= {

    val uf = new UnionFind[Int]

    for (t <- terms)
      uf.makeSet(t)

    // First merge assigned terms
    for ((s, t) <- assignments; if ((terms contains s) && (terms contains t)))
      uf.union(s, t)

    // Fix-point calculation
    var changed = true
    while (changed) {
      changed = false
      // All pairs of eqs, if args_i = args_j, merge s_i with s_j
      for (eq1 <- eqs; eq2 <- eqs;
        if (eq1.fun == eq2.fun && uf(eq1.res) != uf(eq2.res))) {
        var argsEquals = true
        for (i <- 0 until eq1.args.length) {
          if (uf(eq1.args(i)) != uf(eq2.args(i)))
            argsEquals = false
        }
        if (argsEquals) {
          uf.union(eq1.res, eq2.res)
          changed = true
        }
      }
    }

    uf
  }
}




