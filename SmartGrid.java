//import plot.*;

import java.util.*;

import modelchecking.*;
import plot.*;
import flanagan.integration.*;
import formulae.*;
import automata.*;
import automata.actions.*;
import automata.functions.*;

class V{
  public static final int MAX_CONSUMER_BOUND = 20;
  public static final int NUM_GENERATORS = 1;
  
  public static final double GENERATOR_FEEDBACK_LOOP = 5; // 5m
  // STATE VARIABLES
  
  public static final int G_DESIRED_OUTPUT = 0;
  public static final int G_CURRENT_OUTPUT = 1;
  public static final int G_MAX_ACCEL = 2;
  public static final int G_SPEEDUP = 3;
  public static final int G_MAX_SPEEDUP = 4;
  public static final int G_LAST_MESSAGE = 5;
  public static final int G_ID = 6;
  public static final int G_TIME = 7;
  
  public static final int CONS_TIME = 0;
  public static final int CONS_LAST_MESSAGE = 1;
  public static final int CONS_CONSUMPTION = 2;
  public static final int CONS_SPEEDUP = 3;
  public static final int CONS_MAX_SPEEDUP = 4;
  public static final int CONS_MAX_ACCEL = 5;
  public static final int CONS_DECCEL_TIME = 6;
  public static final int CONS_ID = 7;
  
  public static final int CC_NUM_ELEMS = 20;
  public static final int CC_TIME = CC_NUM_ELEMS + 0;
  
  // EDGE NUMBERS
  public static final int PC_CONSUMPTION_EDGE = 0;
  public static final int PC_GEN_FB_EDGE = 1;
  public static final int PC_SEND_MSG_EDGE = 2;
  
  public static final int CONS_SEND_EDGE = 0;
  public static final int CONS_PREPARE_DEATH_EDGE = 1;
  
  public static final int CC_FEEDBACK_EDGE = 0;
  public static final int CC_CREATE_EDGE = 1;
  
  public static final int G_PC_FEEDBACK_EDGE = 0;
  public static final int G_PC_UPDATE_EDGE = 1;
  
  // CHANNEL NAMES
  public static final String GEN_CHAN_PREFIX = "@gen_";
  public static final String GEN_FEEDBACK_CHAN = "@genfb";
  public static final String CONSUMPTION_CHAN = "@power"; // consumption
  public static final String CONSUMER_DEATH_CHAN = "@cdeath"; // consumption
  
}

public class SmartGrid {
  
  public static void printArray(double[] y){
    for(int i = 0; i < y.length; i++)
      System.out.print((int)y[i] + " ");
    System.out.println();
  }
  
  public static void testGenerator(){
    double[] y = new double[5];
    /*y[V.G_DESIRED_OUTPUT] = 100;
    y[V.G_CURRENT_OUTPUT] = 0;
    y[V.G_MAX_ACCEL] = 10;
    y[V.G_SPEEDUP] = 50;
    y[V.G_MAX_SPEEDUP] = 50;*/
    
    y[V.G_DESIRED_OUTPUT] = 100;
    y[V.G_CURRENT_OUTPUT] = 200;
    y[V.G_MAX_ACCEL] = 10;
    y[V.G_SPEEDUP] = 0;
    y[V.G_MAX_SPEEDUP] = 100;
    
    // Set values needed by fixed step size method

    DerivnFunction dvn = new GeneratorEvolution();
    
    double[][] plot = new double[100][];
    for(int i = 0; i < 100; i++){
      plot[i] = RungeKutta.fourthOrder(dvn, 0, y, i*0.1, 1);
      printArray(plot[i]);
    }
    String names[] = {"Desired output", "Current output", "Max acceleration", "Speedup", "Max Speedup"};
    ChartPlot.plot(plot, names, "Marvelous Plotting", "Time", "input");
  }
  
  public static void testConsumer(){
    double[] y = new double[8];
    y[V.CONS_TIME] = 0;
    y[V.CONS_LAST_MESSAGE] = 0;
    y[V.CONS_CONSUMPTION] = 0;
    y[V.CONS_SPEEDUP] = 0;
    y[V.CONS_ID] = 0;
    y[V.CONS_MAX_SPEEDUP] = 2;
    y[V.CONS_MAX_ACCEL] = 0.05;
    y[V.CONS_DECCEL_TIME] = 100;
    //y[V.CONS_MAX_SPEEDUP] = 0.2;
    //y[V.CONS_MAX_ACCEL] = 0.001;
    //y[V.CONS_DECCEL_TIME] = 300;

    DerivnFunction dvn = new ConsumerEvolution();
    
    double[][] plot = new double[1440][];
    for(int i = 0; i < 1440; i++){
      plot[i] = RungeKutta.fourthOrder(dvn, 0, y, i, 1);
      //plot[i][V.CONS_TIME] = plot[i][V.CONS_TIME] / 60;
      //printArray(plot[i]);
      System.out.println(i);
    }
    String names[] = {"Time", "Last Message Time", "Consumption", "Speedup", "Max Speedup", "Max Acceleration", "Decelleration time", "ID"};
    ChartPlot.plot(plot, names, "Marvelous Plotting", "Time", "input");
  }
  
  public static void testConsumers(){
    RandGen.initialise();
    HybridAutomaton ha = new HybridAutomaton();
    
    Location ccLocation = new Location(new PositiveGaussianDistribution(5, 1), new CCDistribution(), new CCEvolution(), 1);
    Location consLocation = new Location(new PositiveGaussianDistribution(5, 3), new ConsumerTransitionDist(), new ConsumerEvolution(), 0.1);
    Location graveyard = new Location(null, new ProbStay(-1), null, 0.1);
    
    Edge ccFeedback = new Edge(ccLocation, ccLocation, null, new ReceiveAction(new CCtrlFeedbackEdge()));
    Edge ccCreate = new Edge(ccLocation, ccLocation, new CCtrlCreateJump(), new NewAction(new CCtrlCreateAction(consLocation)));
    
    Edge cFeedback = new Edge(consLocation, consLocation, new ConsumerFeedbackJump(), new SendAction(new ConsumerFeedbackSend()));
    Edge cDeathPrep = new Edge(consLocation, graveyard, new IdentityJump(), new SendAction(new ConsumerDeathSend()));
    
    Edge scythe = new Edge(graveyard, graveyard, new IdentityJump(), new DieAction());
    
    Edge[] ccEdges = {ccFeedback, ccCreate};
    ccLocation.setEdges(ccEdges);
    
    Edge[] cEdges = {cFeedback, cDeathPrep};
    consLocation.setEdges(cEdges);
    
    Edge[] gEdges = {scythe};
    graveyard.setEdges(gEdges);
    
    ha.addLocation(ccLocation);
    ha.addLocation(consLocation);
    ha.addLocation(graveyard);
    
    ha.addStartingElement(new Element(new State(new double[21]), ccLocation));
    
    Trace t = ha.run(1440);
    //System.out.println(t);
    
    int tsize = t.size();
    double[][] TC = new double[tsize][];
    double[] time = new double[tsize];
    double ctime = 0;
    for(int i = 0; i < tsize; i++){
      double res = 0;
      int nElems = 0;
      for(Element e : t.getState().as.getElements())
        if(e.getState().getState().length < 15){
          res += e.getState().getVar(V.CONS_CONSUMPTION);
          nElems++;
        }
      
      double[] c = {res, nElems * 100};
      TC[i] = c;
      time[i] = ctime / 60;
      ctime = ctime + t.getState().t;
      t.step();
    }
    
    String[] names = {"Power consumption", "# Elems * 100"};
    ChartPlot.xyplot(TC, time, names, "Power consumption", "Time (hours)", "Power consumption");
  }
  
  public static void testConsumersPC(){
    RandGen.initialise();
    HybridAutomaton ha = new HybridAutomaton();
    
    Location pcLocation = new Location(new PositiveGaussianDistribution(5, 1), new PCTransDist(), null, 0.1);
    Location ccLocation = new Location(new PositiveGaussianDistribution(5, 1), new CCDistribution(), new CCEvolution(), 0.1);
    Location consLocation = new Location(new PositiveGaussianDistribution(5, 3), new ConsumerTransitionDist(), new ConsumerEvolution(), 0.1);
    Location graveyard = new Location(null, new ProbStay(-1), null, 0.1);
    Location genLocation = new Location(new PositiveGaussianDistribution(5, 3), new GeneratorTransitionDist(), new GeneratorEvolution(), 0.1);
    
    Edge pcConsFeedback = new Edge(pcLocation, pcLocation, null, new ReceiveAction(new PCConsFeedback()));
    Edge pcGenFeedback = new Edge(pcLocation, pcLocation, null, new ReceiveAction(new PCGenFeedback()));
    Edge pcSendReq = new Edge(pcLocation, pcLocation, new PCRequestChangeJump(), new SendAction(new PCRequestChangeMessage()));
    
    Edge ccFeedback = new Edge(ccLocation, ccLocation, null, new ReceiveAction(new CCtrlFeedbackEdge()));
    Edge ccCreate = new Edge(ccLocation, ccLocation, new CCtrlCreateJump(), new NewAction(new CCtrlCreateAction(consLocation)));
    
    Edge cFeedback = new Edge(consLocation, consLocation, new ConsumerFeedbackJump(), new SendAction(new ConsumerFeedbackSend()));
    Edge cDeathPrep = new Edge(consLocation, graveyard, new IdentityJump(), new SendAction(new ConsumerDeathSend()));
    Edge scythe = new Edge(graveyard, graveyard, new IdentityJump(), new DieAction());
    
    Edge gFeedback = new Edge(genLocation, genLocation, new GeneratorFeedbackJump(), new SendAction(new GeneratorFeedbackSend()));
    Edge gRcvReq = new Edge(genLocation, genLocation, null, new ReceiveAction(new GeneratorMsgRcvJump()));
    
    Edge[] pcEdges = {pcConsFeedback, pcGenFeedback, pcSendReq}; pcLocation.setEdges(pcEdges);
    Edge[] ccEdges = {ccFeedback, ccCreate}; ccLocation.setEdges(ccEdges);
    Edge[] cEdges = {cFeedback, cDeathPrep}; consLocation.setEdges(cEdges);
    Edge[] grEdges = {scythe}; graveyard.setEdges(grEdges);
    Edge[] gEdges = {gFeedback, gRcvReq}; genLocation.setEdges(gEdges);
    
    ha.addLocation(pcLocation);
    ha.addLocation(ccLocation);
    ha.addLocation(consLocation);
    ha.addLocation(graveyard);
    ha.addLocation(genLocation);
    
    ha.addStartingElement(new Element(new State(new double[V.NUM_GENERATORS + 2*V.MAX_CONSUMER_BOUND]), pcLocation)); // Power Controller
    ha.addStartingElement(new Element(new State(new double[21]), ccLocation)); // Consumer Controller
    double[] y1 = new double[9];  y1[V.G_MAX_ACCEL] = 3; y1[V.G_MAX_SPEEDUP] = 20; 
    ha.addStartingElement(new Element(new State(y1), genLocation)); // Generator
    //double[] y2 = new double[9];  y2[V.G_MAX_ACCEL] = 3; y2[V.G_MAX_SPEEDUP] = 20; y2[V.G_ID] = 1;
    //ha.addStartingElement(new Element(new State(y2), genLocation)); // Generator

    Trace t = ha.run(1440);
    //System.out.println(t);
    
    int tsize = t.size();
    double[][] TC = new double[tsize][];
    double[] time = new double[tsize];
    double ctime = 0;
    for(int i = 0; i < tsize; i++){
      double res = 0;
      int nElems = 0;
      double estimatedConsumption = 0;
      //double estimatedProduction = 0;
      double actualProduction = 0;
      for(Element e : t.getState().as.getElements()){
        if(e.getState().getState().length == 8){
          res += e.getState().getVar(V.CONS_CONSUMPTION);
          nElems++;
        } else if(e.getState().getState().length == V.NUM_GENERATORS + 2*V.MAX_CONSUMER_BOUND){ // PC
          for(int j = 0; j < V.MAX_CONSUMER_BOUND; j++)
            estimatedConsumption += e.getState().getVar(PCTransDist.getConsumer(j));
        } else if(e.getState().getState().length == 9){ // generator
          actualProduction += e.getState().getVar(V.G_CURRENT_OUTPUT);
        }
      }
      
      double[] c = {res, nElems * 100, estimatedConsumption, actualProduction};
      TC[i] = c;
      time[i] = ctime / 60;
      ctime = ctime + t.getState().t;
      t.step();
    }
    
    String[] names = {"Power consumption", "# Elems * 100", "Estimated Consumption", "Actual energy output"};
    ChartPlot.xyplot(TC, time, names, "Smart Grid", "Time (hours)", "Electricity");
  }
  
  public static void statisticalMC(){
    RandGen.initialise();
    HybridAutomaton ha = new HybridAutomaton();
    
    Location pcLocation = new Location(new PositiveGaussianDistribution(5, 1), new PCTransDist(), null, 0.1);
    Location ccLocation = new Location(new PositiveGaussianDistribution(5, 1), new CCDistribution(), new CCEvolution(), 0.1);
    Location consLocation = new Location(new PositiveGaussianDistribution(5, 3), new ConsumerTransitionDist(), new ConsumerEvolution(), 0.1);
    Location graveyard = new Location(null, new ProbStay(-1), null, 0.1);
    Location genLocation = new Location(new PositiveGaussianDistribution(5, 3), new GeneratorTransitionDist(), new GeneratorEvolution(), 0.1);
    
    Edge pcConsFeedback = new Edge(pcLocation, pcLocation, null, new ReceiveAction(new PCConsFeedback()));
    Edge pcGenFeedback = new Edge(pcLocation, pcLocation, null, new ReceiveAction(new PCGenFeedback()));
    Edge pcSendReq = new Edge(pcLocation, pcLocation, new PCRequestChangeJump(), new SendAction(new PCRequestChangeMessage()));
    
    Edge ccFeedback = new Edge(ccLocation, ccLocation, null, new ReceiveAction(new CCtrlFeedbackEdge()));
    Edge ccCreate = new Edge(ccLocation, ccLocation, new CCtrlCreateJump(), new NewAction(new CCtrlCreateAction(consLocation)));
    
    Edge cFeedback = new Edge(consLocation, consLocation, new ConsumerFeedbackJump(), new SendAction(new ConsumerFeedbackSend()));
    Edge cDeathPrep = new Edge(consLocation, graveyard, new IdentityJump(), new SendAction(new ConsumerDeathSend()));
    Edge scythe = new Edge(graveyard, graveyard, new IdentityJump(), new DieAction());
    
    Edge gFeedback = new Edge(genLocation, genLocation, new GeneratorFeedbackJump(), new SendAction(new GeneratorFeedbackSend()));
    Edge gRcvReq = new Edge(genLocation, genLocation, null, new ReceiveAction(new GeneratorMsgRcvJump()));
    
    Edge[] pcEdges = {pcConsFeedback, pcGenFeedback, pcSendReq}; pcLocation.setEdges(pcEdges);
    Edge[] ccEdges = {ccFeedback, ccCreate}; ccLocation.setEdges(ccEdges);
    Edge[] cEdges = {cFeedback, cDeathPrep}; consLocation.setEdges(cEdges);
    Edge[] grEdges = {scythe}; graveyard.setEdges(grEdges);
    Edge[] gEdges = {gFeedback, gRcvReq}; genLocation.setEdges(gEdges);
    
    ha.addLocation(pcLocation);
    ha.addLocation(ccLocation);
    ha.addLocation(consLocation);
    ha.addLocation(graveyard);
    ha.addLocation(genLocation);
    
    ha.addStartingElement(new Element(new State(new double[V.NUM_GENERATORS + 2*V.MAX_CONSUMER_BOUND]), pcLocation)); // Power Controller
    ha.addStartingElement(new Element(new State(new double[21]), ccLocation)); // Consumer Controller
    double[] y1 = new double[9];  y1[V.G_MAX_ACCEL] = 3; y1[V.G_MAX_SPEEDUP] = 20; 
    ha.addStartingElement(new Element(new State(y1), genLocation)); // Generator
    
    ITerm output = new TAggSum("e", new TMult(new TTypeIndicator("e", 9), new TVar("e", V.G_CURRENT_OUTPUT)));
    ITerm consumption = new TAggSum("e", new TMult(new TTypeIndicator("e", 8), new TVar("e", V.CONS_CONSUMPTION)));
    ITerm estimatedConsumption = new TAggSum("e", new TMult(new TTypeIndicator("e", V.NUM_GENERATORS + 2*V.MAX_CONSUMER_BOUND),
                                  new TSum(new TVar("e", 0),
                                  new TSum(new TVar("e", 1),
                                  new TSum(new TVar("e", 2),
                                  new TSum(new TVar("e", 3),
                                  new TSum(new TVar("e", 4),
                                  new TSum(new TVar("e", 5),
                                  new TSum(new TVar("e", 6),
                                  new TSum(new TVar("e", 7),
                                  new TSum(new TVar("e", 8),
                                  new TSum(new TVar("e", 9),
                                  new TSum(new TVar("e", 10),
                                  new TSum(new TVar("e", 11),
                                  new TSum(new TVar("e", 12),                                      
                                  new TSum(new TVar("e", 13),
                                  new TSum(new TVar("e", 14),
                                  new TSum(new TVar("e", 15),
                                  new TSum(new TVar("e", 16),
                                  new TSum(new TVar("e", 17),
                                  new TSum(new TVar("e", 18), new TVar("e", 19))))))))))))))))))))));
    ITerm diff = new TAbs(new TSub(output, consumption));
    IFormula f = new FAlways(new PLEQ(diff, new TConst(400)), 60*24);
    
    ITerm diff2 = new TAbs(new TSub(estimatedConsumption, consumption));
    IFormula f2 = new FAlways(new PLEQ(diff2, new TConst(250)), 60*24);
    
    EstimationResult r = Statistical.IntervalEstimation(f, ha, 2, 3, 0.01, 0.99);
    System.out.println(r);
    EstimationResult r2 = Statistical.IntervalEstimation(f2, ha, 2, 3, 0.01, 0.99);
    System.out.println(r2);
  }
  
  public static void main(String[] args){
    //testGenerator();
    //testConsumer();
    //testConsumers();
    testConsumersPC();
    //statisticalMC();
  }
  
  
  
  
  HybridAutomaton buildAutomaton(){
    HybridAutomaton ha = new HybridAutomaton();
    
    /*******************
     *** ENVIRONMENT ***
     *******************/
    
    /************************
     *** POWER CONTROLLER ***
     ************************/
    
    /******************
     *** GENERATORS ***
     ******************/
    
    //Location gen = new Location();
    
    return ha;
  }  
}

/***************
 *** GENERIC ***
 ***************/

class ProbStay implements ITransitionDistribution {
  private double p;
  public ProbStay(double p){ this.p = p; }
  public int draw(State s, MessageLayer ml) { return (RandGen.uniform() < p) ? -1 : 0;}
}

class IdentityJump implements IJumpFunction {
  public State transition(State s) {
    return s; // TODO: maybe we need to do a deep copy, not sure
  }
}

/*******************
 *** ENVIRONMENT ***
 *******************/

/**** CONSUMER ****/

class ConsumerEvolution implements DerivnFunction {
  public double[] derivn(double t, double[] y){
    double res[] = new double[y.length];
    res[V.CONS_TIME] = 1;
    res[V.CONS_CONSUMPTION] = y[V.CONS_SPEEDUP];
    
    if(y[V.CONS_TIME] > y[V.CONS_DECCEL_TIME]){ // If we are deccelerating, then we'll smooth out the descent to 0.
      double sqrt = Math.pow(y[V.CONS_SPEEDUP], 2) - 2*(y[V.CONS_MAX_ACCEL])*y[V.CONS_CONSUMPTION];
      if(sqrt > 0 && (
          (-y[V.CONS_SPEEDUP] - Math.sqrt(sqrt))/(y[V.CONS_MAX_ACCEL]) > 0 ||
          (-y[V.CONS_SPEEDUP] + Math.sqrt(sqrt))/(y[V.CONS_MAX_ACCEL]) > 0)){
        res[V.CONS_SPEEDUP] = y[V.CONS_MAX_ACCEL];
      } else
        res[V.CONS_SPEEDUP] = -y[V.CONS_MAX_ACCEL];
    } else
      res[V.CONS_SPEEDUP] = y[V.CONS_MAX_ACCEL];
   
    // If we're going too fast either up or down, acceleration is now 0.
    if((y[V.CONS_SPEEDUP] >  y[V.CONS_MAX_SPEEDUP] && res[V.CONS_SPEEDUP] > 0) ||
       (y[V.CONS_SPEEDUP] < -y[V.CONS_MAX_SPEEDUP] && res[V.CONS_SPEEDUP] < 0))
       res[V.CONS_SPEEDUP] = 0;
    
    return res;
  }
}

class ConsumerTransitionDist implements ITransitionDistribution {
  private static double MIN_OUTPUT = 1;
  public int draw(State s, MessageLayer ml) {
    // Unconditionally die if the power request is getting too close to 0, after starting to deccelerate
    if(s.getVar(V.CONS_CONSUMPTION) < MIN_OUTPUT && s.getVar(V.CONS_TIME) > s.getVar(V.CONS_DECCEL_TIME))
      return V.CONS_PREPARE_DEATH_EDGE;
    
    // Probability of sending a message to the power controller increases
    // as the distance to the last message increases
    double sendProb = Math.pow((s.getVar(V.CONS_TIME) - s.getVar(V.CONS_LAST_MESSAGE)) / V.GENERATOR_FEEDBACK_LOOP, 10);
    double p = RandGen.uniform();
    if(p < sendProb)
      return V.CONS_SEND_EDGE;
    
    // Else, evolve continuously
    return -1;
  }
}

// Continuous evolution uses pre-made classes

// Sends a message that it's going to die, using identity jump
class ConsumerDeathSend implements ISendFunction {
  public Message newMessage(State s) {
    double[] payload = {s.getVar(V.CONS_ID)};
    return new Message(channel(s), new State(payload));
  }

  public String channel(State s) { return V.CONSUMER_DEATH_CHAN; }
}

// Send feedback to power controller
class ConsumerFeedbackSend implements ISendFunction {
  public Message newMessage(State s) {
    double[] payload = {s.getVar(V.CONS_ID), s.getVar(V.CONS_CONSUMPTION)};
    return new Message(channel(s), new State(payload));
  }

  public String channel(State s) { return V.CONSUMPTION_CHAN; }
}
// Update the last sent message time
class ConsumerFeedbackJump implements IJumpFunction {
  public State transition(State s) {
    State result = new State(s);
    result.setVar(V.CONS_LAST_MESSAGE, s.getVar(V.CONS_TIME));
    return result;
  }  
}

/**** CONSUMER CONTROLLER ****/

// Upon receiving feedback (always about death), update internal state
class CCtrlFeedbackEdge implements IReceiveFunction {
  public State transition(State state, State payload) {
    State newState = new State(state);
    newState.setVar((int)payload.getVar(0), 0);
    return newState;
  }

  public String channel(State s) { return V.CONSUMER_DEATH_CHAN; }
}

// When one creates a new consumer, we update internal state to remember that consumer occupied
class CCtrlCreateJump implements IJumpFunction {
  public State transition(State s) {
    State result = new State(s);
    int firstEmpty= 0;
    while(result.getVar(firstEmpty) == 1)
      firstEmpty++;
    result.setVar(firstEmpty, 1);
    return result;
  }
}

// What parameters to create the new element with
class CCtrlCreateAction implements INewFunction {
  private Location l;
  public CCtrlCreateAction(Location l) { this.l = l; }
  public Element newElement(State s) {
    double []result = new double[8];
    int firstEmpty = 0;
    while(s.getVar(firstEmpty) == 1)
      firstEmpty++;
 
    result[V.CONS_TIME] = 0;
    result[V.CONS_LAST_MESSAGE] = 0;
    result[V.CONS_CONSUMPTION] = 0;
    result[V.CONS_SPEEDUP] = 0;
    result[V.CONS_ID] = firstEmpty;
    
    double cTime = s.getVar(V.CC_TIME);
    if(cTime > 60 * 4 && cTime < 60 * 12) { // During the day
      result[V.CONS_MAX_SPEEDUP] = 2;
      result[V.CONS_MAX_ACCEL] = 0.05;
      result[V.CONS_DECCEL_TIME] = 120;
    } else {
      result[V.CONS_MAX_SPEEDUP] = 0.2;
      result[V.CONS_MAX_ACCEL] = 0.001;
      result[V.CONS_DECCEL_TIME] = 300;
    }
    return new Element(new State(result), l);
  }
}

// Continuous evolution given by one of the generic distributions
// How do we transition?
class CCDistribution implements ITransitionDistribution {
                                  //1,   2,    3,    4,   5,   6,   7,   8,   9,   10,  11,  
  private static double[] pVector= {0.2, 0.05, 0.07, 0.1, 0.1, 0.2, 0.1, 0.2, 0.1, 0.2, 0.1,
                                  //12,  13,  14,  15,  16,  17,   18,   19,   20,   21,   22,   23,   24
                                    0.2, 0.1, 0.2, 0.2, 0.1, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00};
  
  public int draw(State s, MessageLayer ml) {
    if(ml.hasMessage(V.CONSUMER_DEATH_CHAN))
      return V.CC_FEEDBACK_EDGE;
    
    boolean isFree = false;
    for(int i = 0; i < V.CC_NUM_ELEMS; i++)
      if(s.getVar(i) == 0){ isFree = true; break; }
    
    double cTime = s.getVar(V.CC_TIME);
    double p = pVector[(int)(cTime / 60)];
    
    if(RandGen.uniform() < p && isFree)
      return V.CC_CREATE_EDGE;
    else
      return -1;
    
    
  }
}

class CCEvolution implements DerivnFunction {
  public double[] derivn(double t, double[] y){
    double res[] = new double[y.length];
    res[V.CC_TIME] = 1;
    return res;
  }
}

/************************
 *** POWER CONTROLLER ***
 ************************/

class PControllerEvolution implements DerivnFunction {
  private double[] zeros;
  PControllerEvolution(int size){ zeros = new double[size]; }
  public double[] derivn(double t, double[] y){ return zeros; } // all 0s
}

class PCTransDist implements ITransitionDistribution {
  public static final double PROB_MESSAGE_RECEPTION = 0.98;
  public static final double PROB_CONS_VS_GEN = 0.7;
  
  public static final double ABOVE_THRESHOLD = 50;
  public static final double MAX_DEVIATION = 25;
  
  public int draw(State s, MessageLayer ml) {
    double draw = RandGen.uniform();
    if((ml.hasMessage(V.GEN_FEEDBACK_CHAN) || ml.hasMessage(V.CONSUMPTION_CHAN)) && draw < PROB_MESSAGE_RECEPTION){
      if (ml.hasMessage(V.GEN_FEEDBACK_CHAN) && ml.hasMessage(V.CONSUMPTION_CHAN))
        return (RandGen.uniform() < PROB_CONS_VS_GEN) ? V.PC_CONSUMPTION_EDGE : V.PC_GEN_FB_EDGE;
      else if(ml.hasMessage(V.GEN_FEEDBACK_CHAN)) return V.PC_GEN_FB_EDGE;
      else                                        return V.PC_CONSUMPTION_EDGE;
    }
    
    if(Math.abs(estimatedPowerConsumption(s) + ABOVE_THRESHOLD - requestedPowerOutput(s)) > MAX_DEVIATION)
      return V.PC_SEND_MSG_EDGE;

    return -1;
  }
  
  
  public static double requestedPowerOutput(State s){
    double result = 0;
    for(int i = 0; i < V.NUM_GENERATORS; i++)
      result += getRequestedOutput(i, s);
    return result;
  }
  
  public static double estimatedPowerOutput(State s){
    double result = 0;
    for(int i = 0; i < V.NUM_GENERATORS; i++)
      result += getEstimatedOutput(i, s);
    return result;
  }
  
  public static double estimatedPowerConsumption(State s){
    double result = 0;
    for(int i = 0; i < V.MAX_CONSUMER_BOUND; i++)
      result += getConsumer(i, s);
    return result;
  }
  
  public static double getRequestedOutput(int i, State s) { return s.getVar(getRequestedOutput(i));}
  public static double getEstimatedOutput(int i, State s) { return s.getVar(getEstimatedOutput(i));}
  public static double getConsumer(int i, State s){ return s.getVar(getConsumer(i)); }
  
  public static int getRequestedOutput(int i) { return V.MAX_CONSUMER_BOUND + 2*i; }
  public static int getEstimatedOutput(int i) { return V.MAX_CONSUMER_BOUND + 2*i + 1; }
  public static int getConsumer(int i){ return i; }
}

// Sending a message to ask for more power
class PCRequestChangeMessage implements ISendFunction {
  public Message newMessage(State s) {
    int best = chooseBest(s);
    double newRequest = Math.max(0, PCTransDist.estimatedPowerConsumption(s) + PCTransDist.ABOVE_THRESHOLD - (PCTransDist.estimatedPowerOutput(s) - PCTransDist.getEstimatedOutput(best, s)));
    double[] state = {newRequest};
    
    return new Message(channel(s), new State(state));
  }

  public String channel(State s) { return V.GEN_CHAN_PREFIX+chooseBest(s); }
  
  public static int chooseBest(State s){
    if(PCTransDist.estimatedPowerConsumption(s) + PCTransDist.ABOVE_THRESHOLD < PCTransDist.requestedPowerOutput(s)){
      return chooseBestDecrease(s);
    } else {
      return chooseBestIncrease(s);
    }
  }
  public static int chooseBestIncrease(State s){
    int best = 0;
    double min = Double.MAX_VALUE;
    for(int i = 0; i < V.NUM_GENERATORS; i++){
      double diff = Math.abs(PCTransDist.getRequestedOutput(i, s) - PCTransDist.getEstimatedOutput(i, s));
      if(diff < min){
        min = diff;
        best = i;
      }
    }
    return best;
  }
  public static int chooseBestDecrease(State s){
    int best = 0;
    double min = Double.MAX_VALUE;
    for(int i = 0; i < V.NUM_GENERATORS; i++){
      double diff = Math.abs(PCTransDist.getRequestedOutput(i, s) - PCTransDist.getEstimatedOutput(i, s));
      if(PCTransDist.getRequestedOutput(i, s) > PCTransDist.getEstimatedOutput(i, s) && diff < min){
        min = diff;
        best = i;
      }
    }
    return best;
  }
}

class PCRequestChangeJump implements IJumpFunction {
  public State transition(State s) {
    State result = new State(s);
    int best = PCRequestChangeMessage.chooseBest(s);
    double newRequest = Math.max(0, PCTransDist.estimatedPowerConsumption(s) + PCTransDist.ABOVE_THRESHOLD - (PCTransDist.estimatedPowerOutput(s) - PCTransDist.getEstimatedOutput(best, s)));
    result.setVar(PCTransDist.getRequestedOutput(best), newRequest);
    return result;
  }
}

class PCConsFeedback implements IReceiveFunction {

  public String channel(State s) { return V.CONSUMPTION_CHAN; }

  public State transition(State state, State payload) {
    State result = new State(state);
    result.setVar(PCTransDist.getConsumer((int)payload.getVar(0)), payload.getVar(1));
    return result;
  }
}

class PCGenFeedback implements IReceiveFunction {
  public String channel(State s) { return V.GEN_FEEDBACK_CHAN; }

  public State transition(State state, State payload) {
    State result = new State(state);
    result.setVar(PCTransDist.getEstimatedOutput((int)payload.getVar(0)), payload.getVar(1));
    return result;
  }  
}

/******************
 *** GENERATORS ***
 ******************/

class GeneratorEvolution implements DerivnFunction {
  
  public double[] derivn(double t, double[] y) {
    double [] res = new double[y.length];
    res[V.G_CURRENT_OUTPUT] = y[V.G_SPEEDUP];
    res[V.G_TIME] = 1;
    
    if(y[V.G_DESIRED_OUTPUT] > y[V.G_CURRENT_OUTPUT]){ // If we need to produce more
      double sqrt = Math.pow(y[V.G_SPEEDUP], 2) - 2*(-y[V.G_MAX_ACCEL])*(y[V.G_CURRENT_OUTPUT] - y[V.G_DESIRED_OUTPUT]);
      if(sqrt > 0 && (
          (-y[V.G_SPEEDUP] - Math.sqrt(sqrt))/(-y[V.G_MAX_ACCEL]) > 0 ||
          (-y[V.G_SPEEDUP] + Math.sqrt(sqrt))/(-y[V.G_MAX_ACCEL]) > 0)){
        res[V.G_SPEEDUP] = -y[V.G_MAX_ACCEL];
      } else
        res[V.G_SPEEDUP] = y[V.G_MAX_ACCEL];
    } else {
      double sqrt = Math.pow(y[V.G_SPEEDUP], 2) - 2*y[V.G_MAX_ACCEL]*(y[V.G_CURRENT_OUTPUT] - y[V.G_DESIRED_OUTPUT]);
      if(sqrt > 0 && (
          (-y[V.G_SPEEDUP] - Math.sqrt(sqrt))/(y[V.G_MAX_ACCEL]) > 0 ||
          (-y[V.G_SPEEDUP] + Math.sqrt(sqrt))/(y[V.G_MAX_ACCEL]) > 0)){
        res[V.G_SPEEDUP] = y[V.G_MAX_ACCEL];
      } else
        res[V.G_SPEEDUP] = -y[V.G_MAX_ACCEL];
    }
    
    if((y[V.G_SPEEDUP] >  y[V.G_MAX_SPEEDUP] && res[V.G_SPEEDUP] > 0) ||
       (y[V.G_SPEEDUP] < -y[V.G_MAX_SPEEDUP] && res[V.G_SPEEDUP] < 0))
      res[V.G_SPEEDUP] = 0;
    
    return res;
  }
}

class GeneratorTransitionDist implements ITransitionDistribution {
  public static final double PROB_RCV_MESSAGE = 0.98; 
  public int draw(State s, MessageLayer ml) {
    double sendProb = Math.pow((s.getVar(V.G_TIME) - s.getVar(V.G_LAST_MESSAGE)) / V.GENERATOR_FEEDBACK_LOOP, 10);
    double p = RandGen.uniform();
    if(p < sendProb)
      return V.G_PC_FEEDBACK_EDGE;
    
    if(RandGen.uniform() < PROB_RCV_MESSAGE && ml.hasMessage(channel(s)))
      return V.G_PC_UPDATE_EDGE;
    else
      return -1;
  }
  
  public String channel(State s) { return V.GEN_CHAN_PREFIX+(int)s.getVar(V.G_ID); }
}

class GeneratorMsgRcvJump implements IReceiveFunction {
  public State transition(State s, State payload){
    State result = new State(s);
    result.setVar(V.G_DESIRED_OUTPUT, payload.getVar(0));
    return result;
  }

  public String channel(State s) { return V.GEN_CHAN_PREFIX+(int)s.getVar(V.G_ID); }
}

class GeneratorFeedbackSend implements ISendFunction {
  public Message newMessage(State s) {
    double[] payload = {s.getVar(V.G_ID), s.getVar(V.G_CURRENT_OUTPUT)};
    return new Message(channel(s), new State(payload));
  }

  public String channel(State s) { return V.GEN_FEEDBACK_CHAN; }
}
//Update the last sent message time
class GeneratorFeedbackJump implements IJumpFunction {
  public State transition(State s) {
    State result = new State(s);
    result.setVar(V.G_LAST_MESSAGE, s.getVar(V.G_TIME));
    return result;
  }
}











