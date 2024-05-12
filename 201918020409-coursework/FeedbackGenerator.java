public class FeedbackGenerator{
    public static StringBuilder greenCate = new StringBuilder(); //this store the right position number or operators
    public static StringBuilder orangeCate = new StringBuilder();//this store the misplaced number or operators
    public static StringBuilder grayCate = new StringBuilder();//this store the number or operators that is not in the target equations
    public static StringBuilder notUsingCate = new StringBuilder("0123456789+-/*"); // number or operators that not been used by player (For CLI)

    // Method to generate feedback
    //@ requires input != null && targetNumber != null;
    //@ ensures \result != null;
    //@ ensures \result.equals(generateFeedback(input, targetNumber));
    public static String generateFeedback(String input, String targetNumber) {
        //This feedback is for GUI grid labels and CLI
        StringBuilder feedback = new StringBuilder();
        // Create a copy of the targetNumber to track remaining characters and make the feedback more accurate
        StringBuilder remainingTarget = new StringBuilder(targetNumber);

        for (int i = 0; i < input.length(); i++) {
            //compare each character in the guess and answer
            char guessChar = input.charAt(i);
            char targetChar = targetNumber.charAt(i);
            //check green orange and gray for the guess equation
            if (guessChar == targetChar) {
                feedback.append("1");
                //this char is green so delete it from remainingTarget
                deleteFromCate(remainingTarget, guessChar);
                //this char is used, so delete from notUsingCate
                deleteFromCate(notUsingCate, guessChar);
                //add this green char to green Category
                addToCate(greenCate, guessChar);
                //if this char is in the answer but not this place, and the remaining target also have this char, make it orange, make the feedback more precise
            } else if (targetNumber.indexOf(guessChar) != -1 && remainingTarget.indexOf(String.valueOf(guessChar)) != -1) {
                feedback.append("2");
                //add this orange char to orange Category
                addToCate(orangeCate, guessChar);
                deleteFromCate(notUsingCate, guessChar);
            } else {
                feedback.append("3");
                //add this gray char to gray Category
                addToCate(grayCate, guessChar);
                deleteFromCate(notUsingCate, guessChar);
            }
        }
        // if player get some char orange at first, and put them in the right place latter, orange feedback should be cleaned
        // delete the char that in orange also in green
        for (int i = 0; i < greenCate.length(); i++) {
            char ch = greenCate.charAt(i);
            int index = orangeCate.indexOf(String.valueOf(ch));
            if (index != -1) {
                orangeCate.deleteCharAt(index);
            }
        }
        //feedback of categories for CLI and GUI version
        String categories = "Green: " + greenCate + "\n" + "Orange: " + orangeCate + "\n" + "Gray: " + grayCate + "\n" + "Not using: " + notUsingCate;
        return categories + "\n" + feedback;
    }


    // Method to delete a character from a category
    //@ requires cate != null && guessChar >= '0' && guessChar <= '9';
    //@ modifies cate;
    //@ ensures cate.equals(\old(cate).deleteCharAt(\old(cate).indexOf(String.valueOf(guessChar))));
    private static void deleteFromCate(StringBuilder cate, char guessChar){
        // Find the index of the first occurrence of the guessChar in the StringBuilder
        int index1 = cate.indexOf(String.valueOf(guessChar));
        // Check if the guessChar exists in the StringBuilder
        if (index1 != -1) {
            // Check if the guessChar exists in the StringBuilder
            cate.deleteCharAt(index1);
        }
    }
    // Method to add a character to a category
    //@ requires cate != null && guessChar >= '0' && guessChar <= '9';
    //@ modifies cate;
    //@ ensures cate.equals(\old(cate).append(guessChar));
    private static void addToCate(StringBuilder cate, char guessChar){
        // Check if the guessChar does not already exist in the StringBuilder
        if (cate.toString().indexOf(guessChar) == -1) {
            // If the guessChar does not exist, append it to the StringBuilder
            cate.append(guessChar);
        }
    }
}
