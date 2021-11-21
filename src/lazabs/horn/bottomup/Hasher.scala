/**
 * Copyright (c) 2016-2021 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.bottomup

import ap.parameters.ReducerSettings
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.types.Sort
import ap.util.Seqs

import scala.collection.mutable.{ArrayBuffer, BitSet => MBitSet,
                                 HashMap => MHashMap}

object IHasher {

  type Model = Conjunction

}

abstract class IHasher {

  import IHasher.Model

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int

  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit

  def acceptsModels : Boolean

  def isActive : Boolean

  def printStatistics : Unit

  // API for checking satisfaction and implications

  def push : Unit
  def pop : Unit

  def scope[A](comp : => A) : A

  def assertFormula(forId : Int) : Unit

  def isSat : Boolean

  def mightBeImplied(forId : Int) : Boolean

}

////////////////////////////////////////////////////////////////////////////////

object Hasher {

  private abstract sealed class AssertionStackElement

  private case class AssertedFormula(id : Int)
                     extends AssertionStackElement
  private case class AssertionFrame(oldVector : MBitSet)
                     extends AssertionStackElement

  private def setBit(set : MBitSet, index : Int, value : Boolean) : Unit =
    if (value)
      set += index
    else
      set -= index

  private val maxModelNum = 1024

}
object ParHasher{

  private abstract sealed class AssertionStackElement

  private case class AssertedFormula(id : Int)
    extends AssertionStackElement
  private case class AssertionFrame(oldVector : MBitSet)
    extends AssertionStackElement

  private def setBit(set : MBitSet, index : Int, value : Boolean) : Unit =
    if (value)
      set += index
    else
      set -= index

  private val maxModelNum = 1024

}
////////////////////////////////////////////////////////////////////////////////

object InactiveHasher extends IHasher {

  import IHasher._

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int = 0

  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit = throw new UnsupportedOperationException

  def acceptsModels : Boolean = false

  def isActive : Boolean = false

  def printStatistics : Unit = {}

  // API for checking satisfaction and implications

  def push : Unit = {}
  def pop : Unit = {}

  def scope[A](comp : => A) : A = comp

  def assertFormula(forId : Int) : Unit = {}

  // false is a safe answer, since hashing is known to under-approximate
  def isSat : Boolean = false

  def mightBeImplied(forId : Int) : Boolean = true

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to approximate sat and implication checks, by keeping a set of
 * models/structures that are used for evaluating formulas.
 */
class Hasher(globalOrder : TermOrder, reducerSettings : ReducerSettings)
      extends IHasher {

  import Hasher._
  import IHasher._
  private implicit val _globalOrder = globalOrder

  private val watchedFormulas = new ArrayBuffer[Conjunction]
  private val evalVectors     = new ArrayBuffer[MBitSet]

  private val formula2Id      = new MHashMap[Conjunction, Int]

  private val models          = new ArrayBuffer[Model]
  private val reducers        = new ArrayBuffer[ReduceWithConjunction]

  this.synchronized{
    //println("locked block by thread "+ Thread.currentThread.getId())
    // set up some default models
    import TerForConvenience._

    // all variables 0
    models +=
      (for (c <- globalOrder.orderedConstants.toSeq;
            sort = Sort sortOf c;
            constr = sort membershipConstraint LinearCombination.ZERO;
            if !constr.isFalse)
       yield c) === 0

    // all variables distinct, increasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex;
                sort = Sort sortOf c;
                value = l(n+1);
                constr = sort membershipConstraint value;
                if !constr.isFalse)
           yield (c === value))

    // all variables distinct, decreasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex;
                sort = Sort sortOf c;
                value = l(-(n+1));
                constr = sort membershipConstraint value;
                if !constr.isFalse)
           yield (c === value))

    for (m <- models)
      reducers += ReduceWithConjunction(m, globalOrder, reducerSettings)
    //println("unlocked block by thread "+ Thread.currentThread.getId())
  }

  private val presetModelNum = models.size

  //////////////////////////////////////////////////////////////////////////////

  var evalTime : Long = 0
  var evalNum : Int = 0
  def modelNum = this.synchronized{ models.size}

  private def eval(modelIndex : Int, f : Conjunction) : Boolean = this.synchronized{
    //println("locked eval by thread "+ Thread.currentThread.getId())
    import TerForConvenience._

    val startTime = System.currentTimeMillis

    val reduced1 = reducers(modelIndex) tentativeReduce f
    val reduced2 = reducers(0) tentativeReduce reduced1
    val res = reduced2.isTrue

    evalTime = evalTime + (System.currentTimeMillis - startTime)
    evalNum = evalNum + 1

    //println("unlocked eval by thread "+ Thread.currentThread.getId())
    res
  }

  private def mergeModels(modelIndex : Int,
                          model2 : Model) : Option[Model] = this.synchronized{
    //println("locked mergeModels by thread "+ Thread.currentThread.getId())
    import TerForConvenience._
    val ret = if ((reducers(modelIndex) tentativeReduce model2).isFalse) {
      None
    } else {
      val res = models(modelIndex) & model2
      val res2 =
        if (res.predicates.isEmpty)
          res
        else
          ReduceWithConjunction(Conjunction.TRUE, globalOrder,
                                reducerSettings)(res)
      if (res2.isFalse) None else Some(res2)
    }
    //println("unlocked mergeModels by thread "+ Thread.currentThread.getId())
    ret
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int = this.synchronized{
    ap.util.Timer.measure("addFormula") {
      //println("locked addFormula by thread "+ Thread.currentThread.getId())
      val ret = formula2Id.getOrElseUpdate(f, {
        val res = watchedFormulas.size
        watchedFormulas += f

        val evalVector = new MBitSet
        for (i <- (0 until models.size))
          if (eval(i, f))
            evalVector += i
        evalVectors += evalVector

        //    println("Adding " + f + ": " + evalVector)

        res
      })
      //println("unlocked addFormula by thread "+ Thread.currentThread.getId())
      ret
    }
  }
  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit = this.synchronized {
    //println("locked addModel by thread "+ Thread.currentThread.getId())
    //    println("Adding model ...")
    ap.util.Timer.measure("addModel"){
    var i = presetModelNum
    var finished = false

    while (i < models.size && !finished)
      mergeModels(i, model) match {
        case Some(mergedModel) => {
          val changedConstants = model.constants filterNot models(i).constants
          models(i) = mergedModel
          reducers(i) = ReduceWithConjunction(mergedModel, globalOrder, reducerSettings)
          //    println("Merged with #" + i)
          extendModelAndUpdateVectors(i, changedConstants)
          finished = true
        }
        case None =>
          i = i + 1
      }

    if (!finished) {
      i = models.size
      models += model
      reducers += ReduceWithConjunction(model, globalOrder, reducerSettings)
      extendEvalVectors(i)
      //println("now have " + models.size + " models")

    }

    updateAssertionStack(i)
  }
    //println("unlocked addModel by thread "+ Thread.currentThread.getId())
  }

  def acceptsModels : Boolean = this.synchronized{ //println("locked acceptsModels by thread "+ Thread.currentThread.getId())
    val ret = models.size < maxModelNum
    //println("unlocked acceptsModels by thread "+ Thread.currentThread.getId())
    ret
  }

  //////////////////////////////////////////////////////////////////////////////

  private def extendEvalVectors(modelIndex : Int) : Unit = this.synchronized{
    //println("locked extendEvalVectors by thread "+ Thread.currentThread.getId())
    val model = models(modelIndex)
    val assignedConstants = model.constants

    // update the stored vectors
    //make parallel
    for (formulaIndex <- 0 until watchedFormulas.size) {
      val formula = watchedFormulas(formulaIndex)
      val vector = evalVectors(formulaIndex)

      val newBit =
        if (Seqs.disjoint(formula.constants, assignedConstants))
          // use existing model where all constants are assigned 0
          vector(0)
        else
          eval(modelIndex, formula)

      setBit(vector, modelIndex, newBit)
    }
    //println("unlocked extendEvalVectors by thread "+ Thread.currentThread.getId())
  }

  private def extendModelAndUpdateVectors
                         (modelIndex : Int,
                          changedConstants : Set[ConstantTerm]) : Unit = this.synchronized{
    //println("locked extendModelAndUpdateVectors by thread "+ Thread.currentThread.getId())
      val model = models(modelIndex)

      // update the stored vectors
      for (formulaIndex <- 0 until watchedFormulas.size) {
        val formula = watchedFormulas(formulaIndex)
        if (!Seqs.disjoint(formula.constants, changedConstants)) {
          val newBit = eval(modelIndex, formula)
          setBit(evalVectors(formulaIndex), modelIndex, newBit)
        }
      }
    //println("unlocked extendModelAndUpdateVectors by thread "+ Thread.currentThread.getId())
    }

  private def updateAssertionStack(modelIndex : Int) : Unit = this.synchronized{
    //println("locked updateAssertionStack by thread "+ Thread.currentThread.getId())
    var newBit = true
    for (el <- assertionStack) el match {
      case AssertedFormula(id) =>
        newBit = newBit && evalVectors(id)(modelIndex)
      case AssertionFrame(oldVector) =>
        if (oldVector != null)
          setBit(oldVector, modelIndex, newBit)
    }

    if (currentEvalVector != null)
      setBit(currentEvalVector, modelIndex, newBit)
    //println("unlocked updateAssertionStack by thread "+ Thread.currentThread.getId())
  }

  def isActive : Boolean = this.synchronized {true}

  def printStatistics : Unit = this.synchronized{
    //println("locked printStatistics by thread "+ Thread.currentThread.getId())
    println("Number of models in hasher:                            " + modelNum)
    println("Number of hasher evals:                                " + evalNum)
    println("Time for hasher eval:                                  " + evalTime)
    //println("unlocked printStatistics by thread "+ Thread.currentThread.getId())
  }

  //////////////////////////////////////////////////////////////////////////////

  // API for checking satisfaction and implications

  def push : Unit =
    this.synchronized{ //println("locked push by thread "+ Thread.currentThread.getId())
      assertionStack += AssertionFrame(currentEvalVector)
      //println("unlocked push by thread "+ Thread.currentThread.getId())
    }
  def pop : Unit = this.synchronized{
    //println("locked pop by thread "+ Thread.currentThread.getId())
    var i = assertionStack.size - 1
    while (i >= 0) {
      assertionStack(i) match {
        case AssertionFrame(vec) => {
          currentEvalVector = vec
          assertionStack reduceToSize i
          return
        }
        case _ =>
          // nothing
      }
      i = i - 1
    }
    //println("unlocked pop by thread "+ Thread.currentThread.getId())
  }

  def scope[A](comp : => A) : A = {
    //println("locked scope by thread "+ Thread.currentThread.getId())
    push
    val ret = try {
      comp
    } finally {
      pop
    }
    //println("unlocked scope by thread "+ Thread.currentThread.getId())
    ret
  }

  def assertFormula(forId : Int) : Unit = this.synchronized{
    //println("locked assertFormula by thread "+ Thread.currentThread.getId())
    assertionStack += AssertedFormula(forId)
    if (currentEvalVector == null)
      currentEvalVector = evalVectors(forId)
    else
      currentEvalVector = currentEvalVector & evalVectors(forId)
    //println("unlocked assertFormula by thread "+ Thread.currentThread.getId())
  }

  def isSat : Boolean =
    this.synchronized{currentEvalVector == null || !currentEvalVector.isEmpty}

  def mightBeImplied(forId : Int) : Boolean = this.synchronized{
    //println("locked mightBeImplied by thread "+ Thread.currentThread.getId())
    val ret= currentEvalVector != null &&
      (currentEvalVector subsetOf evalVectors(forId))
    //println("unlocked mightBeImplied by thread "+ Thread.currentThread.getId())
    ret
  }
  private var currentEvalVector : MBitSet = null
  private val assertionStack = new ArrayBuffer[AssertionStackElement]

}


class ParHasher(globalOrder : TermOrder, reducerSettings : ReducerSettings)
  extends IHasher {

  import ParHasher._
  import IHasher._
  private implicit val _globalOrder = globalOrder

  private val watchedFormulas = new ArrayBuffer[Conjunction]
  private val evalVectors     = new ArrayBuffer[MBitSet]

  private val formula2Id      = new MHashMap[Conjunction, Int]

  private val models          = new ArrayBuffer[Model]
  private val reducers        = new ArrayBuffer[ReduceWithConjunction]

  this.synchronized{
    //println("locked block by thread "+ Thread.currentThread.getId())
    // set up some default models
    import TerForConvenience._

    // all variables 0
    models +=
      (for (c <- globalOrder.orderedConstants.toSeq;
            sort = Sort sortOf c;
            constr = sort membershipConstraint LinearCombination.ZERO;
            if !constr.isFalse)
      yield c) === 0

    // all variables distinct, increasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex;
                sort = Sort sortOf c;
                value = l(n+1);
                constr = sort membershipConstraint value;
                if !constr.isFalse)
      yield (c === value))

    // all variables distinct, decreasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex;
                sort = Sort sortOf c;
                value = l(-(n+1));
                constr = sort membershipConstraint value;
                if !constr.isFalse)
      yield (c === value))

    for (m <- models)
      reducers += ReduceWithConjunction(m, globalOrder, reducerSettings)
    //println("unlocked block by thread "+ Thread.currentThread.getId())
  }

  private val presetModelNum = models.size

  //////////////////////////////////////////////////////////////////////////////

  var evalTime : Long = 0
  var evalNum : Int = 0
  def modelNum = this.synchronized{ models.size}

  private def eval(modelIndex : Int, f : Conjunction) : Boolean = this.synchronized{
    //println("locked eval by thread "+ Thread.currentThread.getId())
    import TerForConvenience._

    val startTime = System.currentTimeMillis

    val reduced1 = reducers(modelIndex) tentativeReduce f
    val reduced2 = reducers(0) tentativeReduce reduced1
    val res = reduced2.isTrue

    evalTime = evalTime + (System.currentTimeMillis - startTime)
    evalNum = evalNum + 1

    //println("unlocked eval by thread "+ Thread.currentThread.getId())
    res
  }

  private def mergeModels(modelIndex : Int,
                          model2 : Model) : Option[Model] = this.synchronized{
    //println("locked mergeModels by thread "+ Thread.currentThread.getId())
    import TerForConvenience._
    val ret = if ((reducers(modelIndex) tentativeReduce model2).isFalse) {
      None
    } else {
      val res = models(modelIndex) & model2
      val res2 =
        if (res.predicates.isEmpty)
          res
        else
          ReduceWithConjunction(Conjunction.TRUE, globalOrder,
            reducerSettings)(res)
      if (res2.isFalse) None else Some(res2)
    }
    //println("unlocked mergeModels by thread "+ Thread.currentThread.getId())
    ret
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int = this.synchronized {
    //println("locked addFormula by thread "+ Thread.currentThread.getId())
    val ret = formula2Id.getOrElseUpdate(f, {
      val res = watchedFormulas.size
      watchedFormulas += f

      val evalVector = new MBitSet
      evalVector ++= (0 until models.size).par.filter(eval(_,f)).iterator
      evalVectors += evalVector

      //    println("Adding " + f + ": " + evalVector)

      res
    })
    //println("unlocked addFormula by thread "+ Thread.currentThread.getId())
    ret
  }
  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit = this.synchronized{
    //println("locked addModel by thread "+ Thread.currentThread.getId())
    //    println("Adding model ...")
    var i = presetModelNum
    var finished = false

    while (i < models.size && !finished)
      mergeModels(i, model) match {
        case Some(mergedModel) => {
          val changedConstants = model.constants filterNot models(i).constants
          models(i) = mergedModel
          reducers(i) = ReduceWithConjunction(mergedModel, globalOrder, reducerSettings)
          //    println("Merged with #" + i)
          extendModelAndUpdateVectors(i, changedConstants)
          finished = true
        }
        case None =>
          i = i + 1
      }

    if (!finished) {
      i = models.size
      models += model
      reducers += ReduceWithConjunction(model, globalOrder, reducerSettings)
      extendEvalVectors(i)
      //println("now have " + models.size + " models")

    }

    updateAssertionStack(i)
    //println("unlocked addModel by thread "+ Thread.currentThread.getId())
  }

  def acceptsModels : Boolean = this.synchronized{ //println("locked acceptsModels by thread "+ Thread.currentThread.getId())
    val ret = models.size < maxModelNum
    //println("unlocked acceptsModels by thread "+ Thread.currentThread.getId())
    ret
  }

  //////////////////////////////////////////////////////////////////////////////

  private def extendEvalVectors(modelIndex : Int) : Unit = this.synchronized {
    //println("locked extendEvalVectors by thread "+ Thread.currentThread.getId())
    ap.util.Timer.measure("extendEvalVectors"){
    val model = models(modelIndex)
    val assignedConstants = model.constants

    // update the stored vectors
    for (formulaIndex <- 0 until watchedFormulas.size) {
      val formula = watchedFormulas(formulaIndex)
      val vector = evalVectors(formulaIndex)

      val newBit =
        if (Seqs.disjoint(formula.constants, assignedConstants))
        // use existing model where all constants are assigned 0
          vector(0)
        else
          eval(modelIndex, formula)

      setBit(vector, modelIndex, newBit)
    }
  }
    //println("unlocked extendEvalVectors by thread "+ Thread.currentThread.getId())
  }

  private def extendModelAndUpdateVectors
  (modelIndex : Int,
   changedConstants : Set[ConstantTerm]) : Unit = this.synchronized{
    //println("locked extendModelAndUpdateVectors by thread "+ Thread.currentThread.getId())
    val model = models(modelIndex)

    // update the stored vectors
    for (formulaIndex <- 0 until watchedFormulas.size) {
      val formula = watchedFormulas(formulaIndex)
      if (!Seqs.disjoint(formula.constants, changedConstants)) {
        val newBit = eval(modelIndex, formula)
        setBit(evalVectors(formulaIndex), modelIndex, newBit)
      }
    }
    //println("unlocked extendModelAndUpdateVectors by thread "+ Thread.currentThread.getId())
  }

  private def updateAssertionStack(modelIndex : Int) : Unit = this.synchronized{
    //println("locked updateAssertionStack by thread "+ Thread.currentThread.getId())
    var newBit = true
    for (el <- assertionStack) el match {
      case AssertedFormula(id) =>
        newBit = newBit && evalVectors(id)(modelIndex)
      case AssertionFrame(oldVector) =>
        if (oldVector != null)
          setBit(oldVector, modelIndex, newBit)
    }

    if (currentEvalVector != null)
      setBit(currentEvalVector, modelIndex, newBit)
    //println("unlocked updateAssertionStack by thread "+ Thread.currentThread.getId())
  }

  def isActive : Boolean = this.synchronized {true}

  def printStatistics : Unit = this.synchronized{
    //println("locked printStatistics by thread "+ Thread.currentThread.getId())
    println("Number of models in hasher:                            " + modelNum)
    println("Number of hasher evals:                                " + evalNum)
    println("Time for hasher eval:                                  " + evalTime)
    //println("unlocked printStatistics by thread "+ Thread.currentThread.getId())
  }

  //////////////////////////////////////////////////////////////////////////////

  // API for checking satisfaction and implications

  def push : Unit =
    this.synchronized{ //println("locked push by thread "+ Thread.currentThread.getId())
      assertionStack += AssertionFrame(currentEvalVector)
      //println("unlocked push by thread "+ Thread.currentThread.getId())
    }
  def pop : Unit = this.synchronized{
    //println("locked pop by thread "+ Thread.currentThread.getId())
    var i = assertionStack.size - 1
    while (i >= 0) {
      assertionStack(i) match {
        case AssertionFrame(vec) => {
          currentEvalVector = vec
          assertionStack reduceToSize i
          return
        }
        case _ =>
        // nothing
      }
      i = i - 1
    }
    //println("unlocked pop by thread "+ Thread.currentThread.getId())
  }

  def scope[A](comp : => A) : A = {
    //println("locked scope by thread "+ Thread.currentThread.getId())
    push
    val ret = try {
      comp
    } finally {
      pop
    }
    //println("unlocked scope by thread "+ Thread.currentThread.getId())
    ret
  }

  def assertFormula(forId : Int) : Unit = this.synchronized{
    //println("locked assertFormula by thread "+ Thread.currentThread.getId())
    assertionStack += AssertedFormula(forId)
    if (currentEvalVector == null)
      currentEvalVector = evalVectors(forId)
    else
      currentEvalVector = currentEvalVector & evalVectors(forId)
    //println("unlocked assertFormula by thread "+ Thread.currentThread.getId())
  }

  def isSat : Boolean =
    this.synchronized{currentEvalVector == null || !currentEvalVector.isEmpty}

  def mightBeImplied(forId : Int) : Boolean = this.synchronized{
    //println("locked mightBeImplied by thread "+ Thread.currentThread.getId())
    val ret= currentEvalVector != null &&
      (currentEvalVector subsetOf evalVectors(forId))
    //println("unlocked mightBeImplied by thread "+ Thread.currentThread.getId())
    ret
  }
  private var currentEvalVector : MBitSet = null
  private val assertionStack = new ArrayBuffer[AssertionStackElement]

}

/*
class AssertionStackManager{
  /*private abstract sealed class AssertionStackElement
  private case class AssertedFormula(id : Int)
    extends AssertionStackElement
  private val evalVectors     = new ArrayBuffer[MBitSet]*/
  import ParHasher._
  private def updateAssertionStack(modelIndex : Int) : Unit = this.synchronized{
    //println("locked updateAssertionStack by thread "+ Thread.currentThread.getId())
    var newBit = true
    for (el <- assertionStack) el match {
      case AssertedFormula(id) =>
        newBit = newBit && evalVectors(id)(modelIndex)
      case AssertionFrame(oldVector) =>
        if (oldVector != null)
          setBit(oldVector, modelIndex, newBit)
    }

    if (currentEvalVector != null)
      setBit(currentEvalVector, modelIndex, newBit)
    //println("unlocked updateAssertionStack by thread "+ Thread.currentThread.getId())
  }
  def push : Unit =
    this.synchronized{ //println("locked push by thread "+ Thread.currentThread.getId())
      assertionStack += AssertionFrame(currentEvalVector)
      //println("unlocked push by thread "+ Thread.currentThread.getId())
    }
  def pop : Unit = this.synchronized{
    //println("locked pop by thread "+ Thread.currentThread.getId())
    var i = assertionStack.size - 1
    while (i >= 0) {
      assertionStack(i) match {
        case AssertionFrame(vec) => {
          currentEvalVector = vec
          assertionStack reduceToSize i
          return
        }
        case _ =>
        // nothing
      }
      i = i - 1
    }
    //println("unlocked pop by thread "+ Thread.currentThread.getId())
  }
  def scope[A](comp : => A) : A = {
    //println("locked scope by thread "+ Thread.currentThread.getId())
    push
    val ret = try {
      comp
    } finally {
      pop
    }
    //println("unlocked scope by thread "+ Thread.currentThread.getId())
    ret
  }
  def assertFormula(forId : Int) : Unit = this.synchronized{
    //println("locked assertFormula by thread "+ Thread.currentThread.getId())
    assertionStack += AssertedFormula(forId)
    if (currentEvalVector == null)
      currentEvalVector = evalVectors(forId)
    else
      currentEvalVector = currentEvalVector & evalVectors(forId)
    //println("unlocked assertFormula by thread "+ Thread.currentThread.getId())
  }
  private var currentEvalVector : MBitSet = null
  private val assertionStack = new ArrayBuffer[AssertionStackElement]
}*/
