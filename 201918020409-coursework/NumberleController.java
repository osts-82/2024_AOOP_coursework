import javax.swing.*;
import java.awt.*;

// NumberleController.java
public class NumberleController {
    private INumberleModel model;
    private NumberleView view;

    //constructor
    public NumberleController(INumberleModel model) {
        this.model = model;
    }

    public void setView(NumberleView view) {
        this.view = view;
    }

    public void processInput(String input) {
        inputValidator(input);
        model.processInput(input);
        // Check if the game is over
    }

    //check is game is over and have dialog to ask player restart the game
    public void checkGameOver(){
        if (this.isGameOver()) {
            // Display message indicating the result to the user
            if (this.isGameWon()) {
                //a pop-up message box
                JOptionPane.showMessageDialog(view.getFrame(), "Congratulations! You have won!");
            } else {
                JOptionPane.showMessageDialog(view.getFrame(), "Game over! You have run out of attempts.");
            }
            // Optionally, provide an option to start a new game
            int option = JOptionPane.showConfirmDialog(view.getFrame(), "Start a new game?", "New Game", JOptionPane.YES_NO_OPTION);
            if (option == JOptionPane.YES_OPTION) {
                //clear the feedback for grid labels
                view.clearGridFeedback();
                this.startNewGame();
            } else {
                // Exit the application or perform any other action
                System.exit(0);
            }
        }
    }
    public boolean isGameOver() {
        return model.isGameOver();
    }

    public boolean isGameWon() {
        return model.isGameWon();
    }

    public String getTargetWord() {
        return model.getTargetNumber();
    }

    public StringBuilder getCurrentGuess() {
        return model.getCurrentGuess();
    }

    public int getRemainingAttempts() {
        return model.getRemainingAttempts();
    }

    public void startNewGame() {
        model.startNewGame();
    }

    public String getFeedback(){
        return model.getCurrentFeedback();
    }

    public void setRandom(){
        model.setRandomEquationGUI(true);
    }
    public void setNotRandom(){
        model.setRandomEquationGUI(false);
    }

    public void setError(){
        model.setDisplayErrorMessage(true);
    }

    public void unsetError(){
        model.setDisplayErrorMessage(false);
    }

    //the GUI for tell the player input is not valid
    public void inputValidator(String input){
        if (model.isSetErrorMessage()){
            // Validate Equation
            if (!EquationValidator.isValidInput(input)){
                JOptionPane.showMessageDialog(view.getFrame(), "Invalid input! Require 7 digits");
                return;
            }
            if (!EquationValidator.isValidEquation(input)) {
                JOptionPane.showMessageDialog(view.getFrame(), "Invalid Equation");
                return;
            }
        }
    }

    //return bool value to tell if the input is valid
    public boolean isInputValid(String input){
        if (model.isSetErrorMessage()){
            // Validate Equation
            if (!EquationValidator.isValidInput(input)){
                return false;
            }
            if (!EquationValidator.isValidEquation(input)) {
                return false;
            }
        }
        return true;
    }
}