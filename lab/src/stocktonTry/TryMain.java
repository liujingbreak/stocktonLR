package stocktonTry;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

public class TryMain{

    public static void main(String[] args)throws Exception{

        ANTLRInputStream in = new ANTLRInputStream("aaaa");
        StocktonTryLexer lexer = new StocktonTryLexer(in);
    }
}