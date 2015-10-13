package stocktonTry;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.Token;

public class TryMain{

    public static void main(String[] args)throws Exception{

        ANTLRInputStream in = new ANTLRInputStream("987 abc null");
        StocktonTryLexer lexer = new StocktonTryLexer(in);
        System.out.println("start");
        Token tk = lexer.nextToken();
        while(tk.getType() != Token.EOF){
            System.out.println(tk);
            tk = lexer.nextToken();
        }
    }
}