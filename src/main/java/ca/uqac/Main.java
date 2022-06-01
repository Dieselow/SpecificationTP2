package ca.uqac;

import stev.booleans.Implies;
import stev.booleans.Not;
import stev.booleans.And;
import stev.booleans.Or;
import stev.booleans.BooleanFormula;
import stev.booleans.PropositionalVariable;

public class Main {

    public static String SUDOKU = "#26###81#3##7#8##64###5###7#5#1#7#9###39#51###4#3#2#5#1###3###15##2#4##9#38###46#";

    public static void main(String[] args){
       createFormula();
        //   rowConstraints();
       

        System.out.println("Hello world");

    }

    public static void rowConstraints(){
        BooleanFormula formula = null;
        PropositionalVariable[] prop = createPropsLouis();
        //displayArray(prop);
        BooleanFormula fullFormula = null;
        
        for(int j=0;j<9;j++){
            formula = null;
            Not startNot = null;
            for (int i=0;i<8;i++){
                if (startNot == null){
                    startNot = new Not(prop[(i+1)*9+j]);
                    continue;
                }
                else if(formula == null && startNot !=null){
                    formula = new And(startNot,new Not(prop[(i+1)*9+j]));
                }
                else {
                    formula = new And(formula,new Not(prop[(i+1)*9+j]));
                }
            
            }
            //System.out.println(BooleanFormula.toCnf(formula).toString());
            if(fullFormula == null){
                fullFormula = new Implies(prop[j],formula);
                System.out.println(fullFormula);
            }
            else {
                fullFormula = new And(fullFormula,new Implies(prop[j],formula));
            }
        }

       // System.out.println(BooleanFormula.toCnf(fullFormula).toString());
        
    }

    private static PropositionalVariable[] createPropsLouis(){
        PropositionalVariable[] variablesProposition = new PropositionalVariable[9*9*9];
        int row = 1;
        int col = 1;
        int num = 1;
        for(int i=0;i<9*9*9;i++){
            variablesProposition[i] = new PropositionalVariable(String.format("%d%d%d", row, col, num));
            if(num == 9){
                num=1;
                col++;
                if(col > 9){
                    col = 1;
                    row++;
                }
                continue;
            }
        
            num++;
        }
                    
    
        return variablesProposition;
    }
    
    public static void displayArray(PropositionalVariable[] array){
        for (int i = 0; i < array.length; i++) {
            System.out.println(array[i]);
        }
    }
    //Utils
    public static Implies impliesNot(PropositionalVariable i, PropositionalVariable j){
        return new Implies(i, new Not(j));
    }

    private static PropositionalVariable[][][] createVProps(){
        PropositionalVariable[][][] variablesProposition = new PropositionalVariable[9][9][9];
            for(int row=0; row<9; row++){
                for(int col=0; col<9; col++){
                    for(int num=0; num<9; num++){
                        variablesProposition[row][col][num] = new PropositionalVariable(String.format("%d%d%d", row, col, num));
                    } 
                }
            }
        return variablesProposition;
    }

    private static BooleanFormula createFormula(){
        PropositionalVariable[][][] vProps = createVProps();
        BooleanFormula cond1 = createConditionOneNumberByCell(vProps);
        BooleanFormula cond2 = createConditionUniqueNumberByRow(vProps);
        BooleanFormula cond3 = createConditionUniqueNumberByCol(vProps);
        BooleanFormula cond4 = createConditionUniqueNumberSubGrid(vProps);   

        BooleanFormula fullFormula = new And(cond1, cond2, cond3, cond4);

        return fullFormula;
            
    }

    private static BooleanFormula createConditionUniqueNumberByRow(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        for(int row=0; row<9; row++){
            for(int num=0; num<9; num++){
                Or or_row = new Or();
                for(int col=0; col<9; col++){
                    And and_row = new And(vProps[row][col][num]);
                    for(int other_col=0; other_col<8; other_col++){
                        Not n = new Not(vProps[row][(other_col+col+1)%9][num]);
                        and_row = new And(and_row, n);
                    }
                    or_row = new Or(or_row, BooleanFormula.toCnf(and_row));
                }
                fullCondition = new And(fullCondition, or_row);
            }
        }

        return BooleanFormula.toCnf(fullCondition);
    }

    private static BooleanFormula createConditionUniqueNumberByCol(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                Or or_col = new Or();
                for(int num=0; num<9; num++){
                    And and_col = new And(vProps[row][col][num]);
                    for(int other_row=0; other_row<8; other_row++){
                        Not n = new Not(vProps[(other_row+row+1)%9][col][num]);
                        and_col = new And(and_col, n);
                    }
                    or_col = new Or(or_col, BooleanFormula.toCnf(and_col));
                }
                System.out.println(or_col);
                System.exit(0);
                fullCondition = new And(fullCondition, or_col);
            }
        }

        return BooleanFormula.toCnf(fullCondition);
    }
    
    private static BooleanFormula createConditionUniqueNumberSubGrid(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        for(int row=0; row<9; row++){
            for(int num=0; num<9; num++){
                And and_row = new And();
                for(int col=0; col<9; col++){
                    
                }
            }
        }

        return BooleanFormula.toCnf(fullCondition);
    }

    private static BooleanFormula createConditionOneNumberByCell(PropositionalVariable[][][] vProps){
        And fullCondition = new And();

        for(int row=0; row<9; row++){
            for(int col=0; col<9; col++){
                Or or_cell = new Or();

                // Conditions -> Chaque case ne peut contenir qu’un seul chiffre
                // This loop create (1 -2 -3 -4 -5 -6 -7 -8 -9) for each number in one cell
                for(int num=0; num<9; num++){
                    And and_cell = new And(vProps[row][col][num]);
                    // iterate for each other numbers

                    for(int otherNumber=0; otherNumber<8; otherNumber++){
                        Not n = new Not(vProps[row][col][(otherNumber+num+1)%9]);
                        and_cell = new And(and_cell, n);
                    }
                    // Implies cell = new Implies(vProps[row][col][num], BooleanFormula.toCnf(and_cell));
                    // We add the new boolean formula to the others with xor
                    or_cell = new Or(or_cell, and_cell);
                }
                // System.out.println(or_cell);
                // System.out.println(BooleanFormula.toCnf(or_cell));
                // System.exit(0);
                fullCondition = new And(fullCondition, or_cell);
            }
        }
    // System.out.println(BooleanFormula.toCnf(fullCondition));
    return BooleanFormula.toCnf(fullCondition);
    }
}
