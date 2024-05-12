// NumberleView.java
import javax.swing.*;
import java.awt.*;
import java.util.Observer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class NumberleView implements Observer {
    private final INumberleModel MODEL;//Instance of NumberleModel
    private final NumberleController CONTROLLER;//Instance of NumberleController
    private final JFrame FRAME = new JFrame("Numberle");//The current JFrame
    private final JTextField INPUT_TEXT_FIELD = new JTextField();//Input field
    private final JLabel ATTEMPTS_LABEL = new JLabel("Attempts remaining: "); //A label for display the remaining attempts
    private JButton[] operatorButtons; //"+", "-", "*", "/", "="
    private JButton deleteButton; //delete button

    private String greenCate; //Store the green feedback characters form FeedbackGenerator
    private String orangeCate;//Store the orange feedback characters form FeedbackGenerator
    private String grayCate;//Store the gray feedback characters form FeedbackGenerator
    private String greenDigit;//only the green characters without category name
    private String orangeDigit;//only the orange characters without category name
    private String grayDigit;//only the gray characters without category name

    private String gridFeedback=""; //This is a feedback for the 42 gird labels
    private boolean toggle1 = false; //condition for make the random equation button toggleable
    private boolean toggle2 = false;//condition for make the error message check button toggleable
    private JPanel numberPanel; //panel for the input buttons '0-9 +-*/='
    private JLabel[] labels; //grid 42 labels
    private JPanel gridPanel;//panel for the grid labels
    private int currentRow = 0;// the current row of the 42 labels for they have 6 rows x 7 column

    //constructor of view
    public NumberleView(INumberleModel model, NumberleController controller) {
        this.CONTROLLER = controller;
        this.MODEL = model;
        this.CONTROLLER.startNewGame();
        ((NumberleModel)this.MODEL).addObserver(this);
        initializeFrame();
        this.CONTROLLER.setView(this);
        update((NumberleModel)this.MODEL, null);
    }

    //steps for initialize the view
    public void initializeFrame() {
        FRAME.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);//make program exit by click the close button
        FRAME.setSize(600  , 850);// size
        FRAME.setLayout(null);// not use layout
        createGridPanel(); //first part of GUI, grid panel have 42 individual labels
        createInputPanel(); //this is for the input text field and confirm button and submit button
        createFlagPanel(); // this the place to set flags
        createButtonsPanel(); // this is the buttons for '0-9 +-*/='
        FRAME.setVisible(true); //make frame visible
    }


    public void createGridPanel(){
        gridPanel = new JPanel();
        //gird layout 6 x 7
        gridPanel.setLayout(new GridLayout(6,7,2,2));
        // x y position of the frame
        gridPanel.setBounds(1, 1, 580, 380);
        //labels outlook
        labels = new JLabel[42];
        for (int i = 0; i < 42; i++) {
            labels[i] = new JLabel("-");
            Font font = new Font(labels[i].getFont().getFontName(), Font.PLAIN, 26);
            labels[i].setFont(font);
            labels[i].setPreferredSize(new Dimension(65, 65));
            labels[i].setBorder(BorderFactory.createLineBorder(Color.BLACK));
            labels[i].setVerticalAlignment(JLabel.CENTER);
            labels[i].setHorizontalAlignment(JLabel.CENTER);
            labels[i].setForeground(Color.BLACK);
            labels[i].setBackground(Color.white);
            labels[i].setOpaque(true);
            gridPanel.add(labels[i]);
        }
        FRAME.add(gridPanel);
    }

    public void createInputPanel(){
        JPanel inputPanel = new JPanel();
        //look like a stack
        inputPanel.setLayout(new GridLayout(4,1));
        // x y position of the frame
        inputPanel.setBounds(10, 405, 150, 150);
        JButton submitButton = new JButton("Submit"); //submit button
        //action listener of submit
        submitButton.addActionListener(e -> {
            //after the click of submit process intput
            CONTROLLER.processInput(INPUT_TEXT_FIELD.getText());
            //clear the text field
            INPUT_TEXT_FIELD.setText("");
            // Run checkGameOver after the ActionListener finishes execution (not sure if this is useful)
            SwingUtilities.invokeLater(() -> {
                //check if game is won or lose
                CONTROLLER.checkGameOver();
            });
        });
        //this button is for player confirm their guess and put the guess into one of rows in 42 grid labels
        JButton confirmButton = new JButton("Confirm");
        confirmButton.addActionListener(e ->{
            fillTheBlank(INPUT_TEXT_FIELD.getText()); //change the text in label to hold player guess
        });
        inputPanel.add(submitButton);
        inputPanel.add(confirmButton);
        ATTEMPTS_LABEL.setText("Attempts remaining: " + CONTROLLER.getRemainingAttempts());
        inputPanel.add(INPUT_TEXT_FIELD);
        inputPanel.add(ATTEMPTS_LABEL);
        FRAME.add(inputPanel);
    }

    //used for put player guess one of rows in 42 labels
    public void fillTheBlank(String input){
        //check if the input is valid (boolean)
        if(CONTROLLER.isInputValid(input)) {
            char[] chars = input.toCharArray();
            //use currentRow to track which row should the equation go
            for (int i = 0; i < 7; i++) {
                labels[currentRow * 7 + i].setText(Character.toString(chars[i]));
            }
            currentRow++; // Move to next row
            if (currentRow >= 6) {
                currentRow = 0; // Reset currentRow when all rows are filled
            }
        }

    }

    //this is the panel holds three flags buttons
    public void createFlagPanel(){
        JPanel flagPanel = new JPanel();
        //look like a stack
        flagPanel.setLayout(new GridLayout(3, 1));
        // x y position of the frame
        flagPanel.setBounds(10, 645, 150, 150);
        //First Flag Error Message flag
        JButton errorFlag = new JButton("Validate Input");
        errorFlag.addActionListener(e -> {
            toggle2 = !toggle2; //This can make this button toggleable with actual on/close effect
            if(toggle2){
                CONTROLLER.setError(); // activate error message display
                errorFlag.setBackground(Color.WHITE); //make it look like clicked
            } else {
                CONTROLLER.unsetError(); // close error message display
                errorFlag.setBackground(UIManager.getColor("Button.background")); // Reset to default color
            }
        });
        //Second Flag display Equation flag
        JButton displayFlag = new JButton("ShowEquation");
        displayFlag.addActionListener(e -> {
            JOptionPane.showMessageDialog(getFrame(), "Answer Equation is: "+ CONTROLLER.getTargetWord());
        });
        //Third Flag random select equation flag
        JButton randomFlag = new JButton("Random");
        randomFlag.addActionListener(e -> {
            toggle1 = !toggle1;//This can make this button toggleable with actual on/close effect
            if (toggle1) {
                randomFlag.setBackground(Color.WHITE);
                CONTROLLER.setRandom();// activate random selection
            } else {
                randomFlag.setBackground(UIManager.getColor("Button.background")); // Reset to default color
                CONTROLLER.setNotRandom();// disable random selection
            }
        });
        flagPanel.add(errorFlag);
        flagPanel.add(displayFlag);
        flagPanel.add(randomFlag);
        FRAME.add(flagPanel);
    }

    public void createButtonsPanel(){
        numberPanel = new JPanel();
        //organise the 0-9, +-*/= and delete button with a grid layout 4 row x 6 column
        numberPanel.setLayout(new GridLayout(4, 6,10,10));
        // x y position of the frame
        numberPanel.setBounds(170, 400, 400, 400);
        //first generate 0-9 buttons
        for (int i = 0; i < 10; i++) {
            JButton button = new JButton(Integer.toString(i));
            button.setEnabled(true);
            button.addActionListener(e -> {
                //click to show the button value in the text field
                INPUT_TEXT_FIELD.setText(INPUT_TEXT_FIELD.getText() + button.getText());
            });
            //set font for the button
            Font font = new Font(button.getFont().getFontName(), Font.PLAIN, 26);
            button.setFont(font);
            //set background for the button
            button.setBackground(Color.WHITE);
            numberPanel.add(button);
        }
        //the operator buttons
        operatorButtons = new JButton[5];
        String[] operators = {"+", "-", "*", "/", "="};
        for (int i = 0; i < 5; i++) {
            operatorButtons[i] = new JButton(operators[i]);
            int finalI = i;
            operatorButtons[i].addActionListener(e ->{
                INPUT_TEXT_FIELD.setText(INPUT_TEXT_FIELD.getText() + operatorButtons[finalI].getText());
            });
            // Set font size for the button
            Font font = new Font(operatorButtons[i].getFont().getFontName(), Font.PLAIN, 26);
            operatorButtons[i].setFont(font);
            operatorButtons[i].setBackground(Color.WHITE);
            numberPanel.add(operatorButtons[i]);
        }
        FRAME.add(numberPanel);
        //delete button
        deleteButton = new JButton("Delete");
        deleteButton.addActionListener(e -> {
            //set the text of input field to be text - 1, looks like delete last character
            String modifiedText = INPUT_TEXT_FIELD.getText().substring(0, INPUT_TEXT_FIELD.getText().length() - 1);
            INPUT_TEXT_FIELD.setText(modifiedText);
        });
        Font font = new Font("Arial", Font.BOLD, 19);
        deleteButton.setFont(font);
        numberPanel.add(deleteButton);

    }

    //update() method form Observer
    @Override
    public void update(java.util.Observable o, Object arg) {
        //update the remaining attempts
        ATTEMPTS_LABEL.setText("Attempts remaining: " + CONTROLLER.getRemainingAttempts());
        //update the feedback of the keyboard buttons
        colorTheKeyBoardButtons();
        //update the feedback of the grid labels
        colorTheGridPanels();
    }

    //method to color the keyboard buttons base on the feedback
    public void colorTheKeyBoardButtons(){
        //get feedback
        String text = CONTROLLER.getFeedback();
        //split feedback into blocks to further manipulate the string
        String[] parts = text.split("\n");
        //separate the feedback
        greenCate = parts[0];
        orangeCate = parts[1];
        grayCate = parts[2];
        //get the characters in each category
        greenDigit = greenCate.substring(7);
        orangeDigit = orangeCate.substring(8);
        grayDigit = grayCate.substring(7);
        //check the buttons' text to match the feedback
        for (Component component : numberPanel.getComponents()) {
            if (component instanceof JButton) {
                JButton button = (JButton) component;
                String buttonText = button.getText();
                // Check if the button's text matches any character in greenDigit, orangeDigit, or grayDigit
                if (greenDigit.contains(buttonText)) {
                    button.setBackground(Color.GREEN);
                } else if (orangeDigit.contains(buttonText)) {
                    button.setBackground(Color.ORANGE);
                } else if (grayDigit.contains(buttonText)) {
                    button.setBackground(Color.LIGHT_GRAY);
                } else {
                    button.setBackground(Color.WHITE); // Reset color for buttons not used in feedback
                }
            }
        }
    }

    //method to color the grid labels base on the feedback
    public void colorTheGridPanels(){
        //get feedback
        String text = CONTROLLER.getFeedback();
        //split feedback into blocks to further manipulate the string
        String[] parts = text.split("\n");
        //check if is the new game
        if(CONTROLLER.getRemainingAttempts() == 6){
            gridFeedback = "";
        }else {gridFeedback = parts[4];}
        //match the labels' text with the feedback to update the color
        if (!gridFeedback.isEmpty() && gridFeedback.length() >= 7) {
            for (int i = 0; i < 7; i++) {
                if (gridFeedback.charAt(i) == '1'){
                    labels[(currentRow-1) * 7 + i].setBackground(Color.GREEN);
                } else if (gridFeedback.charAt(i) == '2') {
                    labels[(currentRow-1) * 7 + i].setBackground(Color.ORANGE);
                } else if (gridFeedback.charAt(i) == '3') {
                    labels[(currentRow-1) * 7 + i].setBackground(Color.GRAY);
                }else {
                    labels[(currentRow-1) * 7 + i].setBackground(Color.WHITE);
                }
            }
        }

    }
    public JFrame getFrame() {
        return FRAME;
    }

    //method to clear the numbers and color for grid labels
    public void clearGridFeedback(){
        if (CONTROLLER.isGameOver()){
            //clearGridFeedback();
            for (int i = 0; i < 42; i++) {
                labels[i].setBackground(Color.white);
                labels[i].setText("/");
            }
        }
    }

}