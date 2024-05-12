// NumberleModel.java
import java.io.File;
import java.util.*;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

public class NumberleModel extends Observable implements INumberleModel {
    private String targetNumber; //This is the equation answer player need to guess
    private StringBuilder currentGuess; // This is the player's guess equation
    private int remainingAttempts;
    private boolean gameWon;
    //Flags
    private boolean displayErrorMessage = false; // Flag for input validation (error message)

    private boolean displayTargetEquation = false;// Flag for display the equation answer

    private boolean randomEquationSelection = false;// Flag for randomly choose equations

    private List<String> equations; // List to store equations from the file equations.txt

    private int equationIndex; // Index to keep track of the current equation

    //Four separate categories
    private String feedback; // Store the color information of each digit in a equation


    public boolean isSetErrorMessage(){
        return displayErrorMessage; //Check if the error message flag has been set
    }
    // Precondition: None
    // Post-condition: displayErrorMessage == true if and only if displayErrorMessage is set
    //@ requires true;
    //@ ensures isSetErrorMessage() == displayErrorMessage;
    public void setDisplayErrorMessage(boolean displayErrorMessage) {
        this.displayErrorMessage = displayErrorMessage;
    }

    // Precondition: None
    // Post-condition: displayTargetEquation == true if and only if displayTargetEquation is set
    //@ requires true;
    //@ ensures displayTargetEquation == true;
    public void setDisplayTargetEquation(boolean displayTargetEquation) {
        this.displayTargetEquation = displayTargetEquation;
    }
    // Precondition: None
    // Post-condition: randomEquationSelection == true if and only if randomEquationSelection is set
    //@ requires true;
    //@ ensures randomEquationSelection == true;
    public void setRandomEquationSelection(boolean randomEquationSelection) {
        this.randomEquationSelection = randomEquationSelection;
    }


    // Precondition: None
    // Post-condition: randomEquationSelection == b, targetNumber is set according to randomEquationSelection
    //@ requires true;
    //@ ensures randomEquationSelection == b && targetNumber != null && equations != null && equationIndex >= 0 && equationIndex < equations.size();
    public void setRandomEquationGUI(boolean b){
        assert b == true || b == false : "Parameter b must be a boolean value";
        // Store the current values of the fields for comparison
        boolean previousRandomEquationSelection = randomEquationSelection;
        int previousEquationIndex = equationIndex;
        String previousTargetNumber = targetNumber;

        this.randomEquationSelection = b;
        int lastEquation = this.equationIndex;
        readEquationsFromFile("equations.txt");
        if (randomEquationSelection){
            Random random = new Random();
            //Generate a random int in range 0-108
            int randEquation = random.nextInt(108);
            assert randEquation >= 0 && randEquation < 108 : "Random equation index out of bounds";
            equationIndex = randEquation;
        }else {
            equationIndex = lastEquation;
        }
        assert equationIndex >= 0 && equationIndex < equations.size() : "Equation index out of bounds";

        // Set the equation as the targetNumber
        targetNumber = equations.get(equationIndex);

        // Assert that changes have occurred only if the method has been called
        assert previousRandomEquationSelection != randomEquationSelection ||
                previousEquationIndex != equationIndex ||
                !previousTargetNumber.equals(targetNumber) : "No changes occurred in the method";
    }

    // Precondition: None
    // Post-condition: All class fields are initialized
    //@ requires true;
    //@ ensures targetNumber != null && currentGuess != null && remainingAttempts == MAX_ATTEMPTS && gameWon == false;
    @Override
    public void initialize() {
        // Store the current values of the fields for comparison
        int previousRemainingAttempts = remainingAttempts;
        boolean previousGameWon = gameWon;
        String previousFeedback = feedback;

        // Read equations from the file and store them in the equations list
        readEquationsFromFile("equations.txt");
        // Flag for randomly select an equation Used by CLI game.
        if (randomEquationSelection){
            Random random = new Random();
            int randEquation = random.nextInt(108);
            equationIndex = randEquation;
        }else {
            equationIndex = 0;
        }
        // Set the equation as the targetNumber
        targetNumber = equations.get(equationIndex);
        // Flag for display the target equation if the flag is set
        if (displayTargetEquation) {
            System.out.println("Target Equation is: " + targetNumber);
        }
        //now the guess is empty
        currentGuess = new StringBuilder("       ");
        //MAX_ATTEMPTS = 6 in the interface
        remainingAttempts = MAX_ATTEMPTS;
        //Game is not won
        gameWon = false;

        // Assert that all fields are initialized as expected
        assert targetNumber != null : "targetNumber is not initialized";
        assert currentGuess != null && currentGuess.length() == 7 : "currentGuess is not initialized";
        assert remainingAttempts == MAX_ATTEMPTS : "remainingAttempts is not initialized";
        assert !gameWon : "gameWon is not initialized";

        // Assert that changes have occurred only if the method has been called
        assert !previousGameWon != gameWon ||
                !previousFeedback.equals(feedback) : "No changes occurred in the method";

        // Notify observers
        setChanged();
        notifyObservers();
    }

    // Precondition: input is a valid equation
    // Post-condition: currentGuess is updated based on the input
    //@ requires displayErrorMessage == true;
    //@ ensures !isGameOver() ==> (currentGuess.equals(\old(currentGuess).replaceFirst(input)) && remainingAttempts == \old(remainingAttempts) - 1);
    //@ ensures isGameOver() ==> (currentGuess.equals(\old(currentGuess).replaceFirst(input)) && remainingAttempts == 0);
    @Override
    public boolean processInput(String input) {
        //Flag for error message to validate input
        if (displayErrorMessage){
            // Validate if input is 7 digit
            if (!EquationValidator.isValidInput(input)) {
                return false;
            }
            assert EquationValidator.isValidInput(input) : "Input is not 7 digits";
            // check if it is a valid Equation
            if (!EquationValidator.isValidEquation(input)) {
                return false;
            }
            assert EquationValidator.isValidEquation(input) : "Input is not a valid equation";
        }
        // Update the current guess based on the input
        updateCurrentGuess(input);
        // Check if the guess matches the target number
        if (currentGuess.toString().equals(targetNumber)) {
            gameWon = true;
        }
        //use one attempt
        remainingAttempts--;
        if(isGameOver()){
            System.out.println("Game over!");
        }

        // Notify observers
        setChanged();
        notifyObservers();
        return true;
    }

    // Precondition: None
    // Post-condition: true if and only if remainingAttempts <= 0 or gameWon is true
    //@ requires true;
    //@ ensures \result == (remainingAttempts <= 0 || gameWon == true);
    @Override
    public boolean isGameOver() {
        return remainingAttempts <= 0 || gameWon;
    }

    // Precondition: None
    // Post-condition: true if and only if gameWon is true
    //@ requires true;
    //@ ensures \result == gameWon;
    @Override
    public boolean isGameWon() {
        return gameWon;
    }

    // Precondition: None
    // Post-condition: targetNumber is returned
    //@ requires true;
    //@ ensures \result == targetNumber;
    @Override
    public String getTargetNumber() {
        return targetNumber;
    }

    // Precondition: None
    // Post-condition: currentGuess is returned
    //@ requires true;
    //@ ensures \result == currentGuess;
    @Override
    public StringBuilder getCurrentGuess() {
        return currentGuess;
    }

    // Precondition: None
    // Post-condition: remainingAttempts is returned
    //@ requires true;
    //@ ensures \result == remainingAttempts;
    @Override
    public int getRemainingAttempts() {
        return remainingAttempts;
    }

    // Precondition: None
    // Post-condition: All fields are reset and a new game is initialized
    //@ requires true;
    //@ ensures remainingAttempts == \old(MAX_ATTEMPTS) && gameWon == false && feedback == null;
    @Override
    public void startNewGame() {
        // Store the current values of the fields for comparison
        int previousRemainingAttempts = remainingAttempts;
        boolean previousGameWon = gameWon;
        String previousFeedback = feedback;


        clearFeedBack();// when a new game is started, the last game's color need to be clear
        initialize();

        // Assert post-conditions
        assert remainingAttempts == MAX_ATTEMPTS : "remainingAttempts is not reset to MAX_ATTEMPTS";
        assert !gameWon : "gameWon is not reset to false";
        assert feedback == null : "feedback is not reset to null";

        // Assert that changes have occurred only if the method has been called
        assert previousRemainingAttempts != remainingAttempts ||
                previousGameWon != gameWon ||
                !Objects.equals(previousFeedback, feedback) : "No changes occurred in the method";
    }

    // Precondition: None
    // Post-condition: feedback is generated based on currentGuess and targetNumber
    //@ requires true;
    //@ ensures feedback != null;
    @Override
    public String getCurrentFeedback() {
        // Store the current value of feedback for comparison
        String previousFeedback = feedback;

        //pass the player guess equation and the answer to class FeedbackGenerator, return a string contain the categorises
        feedback = FeedbackGenerator.generateFeedback(currentGuess.toString(), targetNumber);

        assert feedback != null : "feedback is not generated";

        return feedback;
    }

    // Precondition: input is not null and input.length() <= currentGuess.length()
    // Post-condition: currentGuess is updated with characters from input
    //@ requires input != null && input.length() <= currentGuess.length();
    //@ modifies currentGuess;
    //@ ensures (\forall int i; 0 <= i && i < input.length(); currentGuess.charAt(i) == input.charAt(i));
    private void updateCurrentGuess(String input) {
        // Store the current value of currentGuess for comparison
        StringBuilder previousCurrentGuess = new StringBuilder(currentGuess);

        // Assert post-condition
        assert input != null && input.length() <= previousCurrentGuess.length() :
                "Pre-condition input length check failed";

        // Loop through each character in the input and update the corresponding position in currentGuess
        for (int i = 0; i < input.length(); i++) {
            char c = input.charAt(i);
            // Update the currentGuess string at position i with the character c
            currentGuess.setCharAt(i, c);
        }
    }

    // Precondition: filename is not null and represents a valid file path
    // Post-condition: equations is initialized with the content read from the file
    //@ requires filename != null;
    //@ requires \fresh(equations);
    //@ ensures equations != null && equations.size() > 0;
    //@ signals (IOException e) false;
    private void readEquationsFromFile(String filename) {

        equations = new ArrayList<>();
        // Start a try block to handle potential IOException
        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            // Declare a variable to store each line read from the file
            String line;
            // Read each line from the file until there are no more lines
            while ((line = br.readLine()) != null) {
                equations.add(line.trim());
            }
            // Assert post-condition
            assert equations != null && equations.size() > 0 : "Equations is not initialized or is empty";
            // Catch any IOException that occurs during file reading
        } catch (IOException e) {
            // Print the stack trace if an IOException occurs
            e.printStackTrace();
            // Assert that the IOException is not signaled
            assert false : "IOException occurred";
        }
        // Assert pre-condition
        assert filename != null : "Filename is null";
        assert new File(filename).exists() : "Filename does not represent a valid file path";
    }

    // Precondition: None
    // Post-condition: FeedbackGenerator.grayCate, FeedbackGenerator.greenCate, and FeedbackGenerator.orangeCate are cleared
    //@ requires true;
    //@ ensures FeedbackGenerator.grayCate.length() == 0 && FeedbackGenerator.greenCate.length() == 0 && FeedbackGenerator.orangeCate.length() == 0;
    public void clearFeedBack(){ // clear feedback, clear each category
        // Store the current values of the feedback categories for comparison
        int previousGrayCateLength = FeedbackGenerator.grayCate.length();
        int previousGreenCateLength = FeedbackGenerator.greenCate.length();
        int previousOrangeCateLength = FeedbackGenerator.orangeCate.length();

        FeedbackGenerator.grayCate.delete(0, FeedbackGenerator.grayCate.length());
        FeedbackGenerator.greenCate.delete(0, FeedbackGenerator.greenCate.length());
        FeedbackGenerator.orangeCate.delete(0, FeedbackGenerator.orangeCate.length());

        // Assert post-condition
        assert FeedbackGenerator.grayCate.length() == 0 : "Gray category is not cleared";
        assert FeedbackGenerator.greenCate.length() == 0 : "Green category is not cleared";
        assert FeedbackGenerator.orangeCate.length() == 0 : "Orange category is not cleared";

        // Assert that changes have occurred only if the method has been called
        assert previousGrayCateLength != FeedbackGenerator.grayCate.length() ||
                previousGreenCateLength != FeedbackGenerator.greenCate.length() ||
                previousOrangeCateLength != FeedbackGenerator.orangeCate.length() :
                "No changes occurred in the method";
    }

}