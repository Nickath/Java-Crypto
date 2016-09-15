/*
	Program to apply Encryption and Decryption of hexadecimal text Using DES algorithm with random generated S boxes
	and sage implementation to
	testify and compare the strength of pseudo-Random generated S-boxes against differential cryptanalysis 
	with the recommended ones using Java

	Author:Nick Athanasiou  https://github.com/Nickath
	References: Manav Sanghavi		http://www.pracspedia.com/INS/DES-java.html
	
*/
import java.io.UnsupportedEncodingException;
import java.math.BigInteger;
import java.util.*;

import javax.xml.bind.DatatypeConverter;

class DES {
	// Initial Permutation table
	private static final byte[] IP = { 
		58, 50, 42, 34, 26, 18, 10, 2,
		60, 52, 44, 36, 28, 20, 12, 4,
		62, 54, 46, 38, 30, 22, 14, 6,
		64, 56, 48, 40, 32, 24, 16, 8,
		57, 49, 41, 33, 25, 17, 9,  1,
		59, 51, 43, 35, 27, 19, 11, 3,
		61, 53, 45, 37, 29, 21, 13, 5,
		63, 55, 47, 39, 31, 23, 15, 7
	};
	
	// Permuted Choice 1 table
	private static final byte[] PC1 = {
		57, 49, 41, 33, 25, 17, 9,
		1,  58, 50, 42, 34, 26, 18,
		10, 2,  59, 51, 43, 35, 27,
		19, 11, 3,  60, 52, 44, 36,
		63, 55, 47, 39, 31, 23, 15,
		7,  62, 54, 46, 38, 30, 22,
		14, 6,  61, 53, 45, 37, 29,
		21, 13, 5,  28, 20, 12, 4
	};
	
	// Permuted Choice 2 table
	private static final byte[] PC2 = {
		14, 17, 11, 24, 1,  5,
		3,  28, 15, 6,  21, 10,
		23, 19, 12, 4,  26, 8,
		16, 7,  27, 20, 13, 2,
		41, 52, 31, 37, 47, 55,
		30, 40, 51, 45, 33, 48,
		44, 49, 39, 56, 34, 53,
		46, 42, 50, 36, 29, 32
	};
	
	// Array to store the number of rotations that are to be done on each round
	private static final byte[] rotations = {
		1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1
	};
	
	// Expansion (aka P-box) table
	private static final byte[] E = {
		32, 1,  2,  3,  4,  5,
		4,  5,  6,  7,  8,  9,
		8,  9,  10, 11, 12, 13,
		12, 13, 14, 15, 16, 17,
		16, 17, 18, 19, 20, 21,
		20, 21, 22, 23, 24, 25,
		24, 25, 26, 27, 28, 29,
		28, 29, 30, 31, 32, 1
	};
	
	
	
	
	
	
	
	// S-boxes (i.e. Substitution boxes)
		private static final byte[][] S = { {
			14, 4,  13, 1,  2,  15, 11, 8,  3,  10, 6,  12, 5,  9,  0,  7,
			0,  15, 7,  4,  14, 2,  13, 1,  10, 6,  12, 11, 9,  5,  3,  8,
			4,  1,  14, 8,  13, 6,  2,  11, 15, 12, 9,  7,  3,  10, 5,  0,
			15, 12, 8,  2,  4,  9,  1,  7,  5,  11, 3,  14, 10, 0,  6,  13
		}, {
			15, 1,  8,  14, 6,  11, 3,  4,  9,  7,  2,  13, 12, 0,  5,  10,
			3,  13, 4,  7,  15, 2,  8,  14, 12, 0,  1,  10, 6,  9,  11, 5,
			0,  14, 7,  11, 10, 4,  13, 1,  5,  8,  12, 6,  9,  3,  2,  15,
			13, 8,  10, 1,  3,  15, 4,  2,  11, 6,  7,  12, 0,  5,  14, 9
		}, {
			10, 0,  9,  14, 6,  3,  15, 5,  1,  13, 12, 7,  11, 4,  2,  8,
			13, 7,  0,  9,  3,  4,  6,  10, 2,  8,  5,  14, 12, 11, 15, 1,
			13, 6,  4,  9,  8,  15, 3,  0,  11, 1,  2,  12, 5,  10, 14, 7,
			1,  10, 13, 0,  6,  9,  8,  7,  4,  15, 14, 3,  11, 5,  2,  12
		}, {
			7,  13, 14, 3,  0,  6,  9,  10, 1,  2,  8,  5,  11, 12, 4,  15,
			13, 8,  11, 5,  6,  15, 0,  3,  4,  7,  2,  12, 1,  10, 14, 9,
			10, 6,  9,  0,  12, 11, 7,  13, 15, 1,  3,  14, 5,  2,  8,  4,
			3,  15, 0,  6,  10, 1,  13, 8,  9,  4,  5,  11, 12, 7,  2,  14
		}, {
			2,  12, 4,  1,  7,  10, 11, 6,  8,  5,  3,  15, 13, 0,  14, 9,
			14, 11, 2,  12, 4,  7,  13, 1,  5,  0,  15, 10, 3,  9,  8,  6,
			4,  2,  1,  11, 10, 13, 7,  8,  15, 9,  12, 5,  6,  3,  0,  14,
			11, 8,  12, 7,  1,  14, 2,  13, 6,  15, 0,  9,  10, 4,  5,  3
		}, {
			12, 1,  10, 15, 9,  2,  6,  8,  0,  13, 3,  4,  14, 7,  5,  11,
			10, 15, 4,  2,  7,  12, 9,  5,  6,  1,  13, 14, 0,  11, 3,  8,
			9,  14, 15, 5,  2,  8,  12, 3,  7,  0,  4,  10, 1,  13, 11, 6,
			4,  3,  2,  12, 9,  5,  15, 10, 11, 14, 1,  7,  6,  0,  8,  13
		}, {
			4,  11, 2,  14, 15, 0,  8,  13, 3,  12, 9,  7,  5,  10, 6,  1,
			13, 0,  11, 7,  4,  9,  1,  10, 14, 3,  5,  12, 2,  15, 8,  6,
			1,  4,  11, 13, 12, 3,  7,  14, 10, 15, 6,  8,  0,  5,  9,  2,
			6,  11, 13, 8,  1,  4,  10, 7,  9,  5,  0,  15, 14, 2,  3,  12
		}, {
			13, 2,  8,  4,  6,  15, 11, 1,  10, 9,  3,  14, 5,  0,  12, 7,
			1,  15, 13, 8,  10, 3,  7,  4,  12, 5,  6,  11, 0,  14, 9,  2,
			7,  11, 4,  1,  9,  12, 14, 2,  0,  6,  10, 13, 15, 3,  5,  8,
			2,  1,  14, 7,  4,  10, 8,  13, 15, 12, 9,  0,  3,  5,  6,  11
		} };
	
	
	// Permutation table
	private static final byte[] P = {
		16, 7,  20, 21,
		29, 12, 28, 17,
		1,  15, 23, 26,
		5,  18, 31, 10,
		2,  8,  24, 14,
		32, 27, 3,  9,
		19, 13, 30, 6,
		22, 11, 4,  25
	};
	
	// Final permutation (aka Inverse permutation) table
	private static final byte[] FP = {
		40, 8, 48, 16, 56, 24, 64, 32,
		39, 7, 47, 15, 55, 23, 63, 31,
		38, 6, 46, 14, 54, 22, 62, 30,
		37, 5, 45, 13, 53, 21, 61, 29,
		36, 4, 44, 12, 52, 20, 60, 28,
		35, 3, 43, 11, 51, 19, 59, 27,
		34, 2, 42, 10, 50, 18, 58, 26,
		33, 1, 41, 9, 49, 17, 57, 25
	};
	
	// 28 bits each, used as storage in the KS (Key Structure) rounds to 
	// generate round keys (aka subkeys)
	private static int[] C = new int[28];
	private static int[] D = new int[28];
	
	// Decryption requires the 16 subkeys to be used in the exact same process
	// as encryption, with the only difference being that the keys are used
	// in reverse order, i.e. last key is used first and so on. Hence, during
	// encryption when the keys are first generated, they are stored in this
	// array. In case we wish to separate the encryption and decryption
	// programs, then we need to generate the subkeys first in order, store
	// them and then use them in reverse order.
	private static int[][] subkey = new int[16][48];
	
	
	//function Generating 8 Random S-boxes for the addressing of the 6bit groups to 4 bit groups
	public  static  byte[][] sboxesGenerator(byte[][] RS)
	{
		for (int i=0; i<8; i++)
		{
			
			String Sbox = String.valueOf(i+1);
			System.out.println("\n\nSbox "+ Sbox +"");
			//System.out.print("[");
			for(int j=0; j<64; j++)
			{
				if(j==16 || j== 32 || j == 48 || j ==64)
				{
					System.out.println();
				}
				Random rg = new Random(); //rg object of class Random, generate pseudo-random numbers from 0 to 15
				int n = rg.nextInt(16);
				RS[i][j] = (byte) n;//store random number byte n into RS table
				if(j<63)
				{
				System.out.print(RS[i][j] + ",");
				}
				else if(j==63)
				{
					System.out.print(RS[i][j] );
				}
			}
		
		
		}
		System.out.println("\n");

		return RS;
		
	}
	
	//the ddtrenewer function fills all elements in DDT table with zeros
	public static int[][] ddtrenewer(int[][] DDT)
	{
		for (int i=0; i<64; i++)
		{
			for(int j=0; j<16; j++)
			{
				DDT[i][j]=0;
			}
		}
		return DDT;
	}
	
	public static double[] RecommendedSboxesE()
	{
				int DDT[][] = new int[64][16] ;
				
				int x1xorx2;
				 int y1xory2 ;
				int stoixeio2SBOX1;
				int count = 0;
				String x1 = "000000";
				String x2;
				byte y1;
				byte y2;
				int xoredvalues = 0;
				int sxoredvalues = 0;
				String xoredstring = "";
				String sxoredstring = "";
				String SBiy1row;
				String SBiy1column;
				int akeraioSBiy1row;
				int akeraioSBiy1column;
				String SBiy2row;
				String SBiy2column;
				int akeraioSBiy2row;
				int akeraioSBiy2column;
				String SBiy2;
				String SBiy="";
				int	R=0;
				int	L=0;
				double	Re[] = new double[8];
				int n=6;//S-box table of type nxs where n =4
				
				System.out.println("RECOMMENDED S-BOXES FOR THE ENCRYPTION-DECRYPTION OF PLAIN-TEXT USING DES ALGORITHM");
			    
			  
					
				//Each pair of 6bit inputs has 64x64 possible pairs of outputs
					
					for(int w=0; w<8; w++)
					{
						
						ddtrenewer(DDT);//calls the ddtrenewer function which fills all elements in DDT table with zeros
						 x1xorx2=0;
						  y1xory2=0; ;
						 stoixeio2SBOX1=0;
						 count = 0;
						 x1 = "000000";
						 x2="";
						 y1=0;
						 y2=0;
						 xoredvalues = 0;
						 sxoredvalues = 0;
						 xoredstring = "";
						 sxoredstring = "";
						 SBiy1row="";
						 SBiy1column="";
						 akeraioSBiy1row=0;
						 akeraioSBiy1column=0;
						 SBiy2row="";
						 SBiy2column="";
					     akeraioSBiy2row=0;
						 akeraioSBiy2column=0;
						 SBiy2="";
						 SBiy="";
						 R=0;
						 L=0;
						 
					 for(int i =0; i<64; i++)
					    {
					    	 x1 = String.format("%06d", Integer.parseInt(x1));//parsarw to string x1 san akeraio kai tou bazw midenika an dn exei 6 psifio stin arxi
							 x2 = "000000";
					    	for(int j=0; j<64; j++)
					    	{
					    		xoredstring = "";
						        SBiy1row = Character.toString(x1.charAt(0)) + Character.toString(x1.charAt(5)) ;
						        SBiy1column = Character.toString(x1.charAt(1)) + Character.toString(x1.charAt(2)) +Character.toString(x1.charAt(3)) + Character.toString(x1.charAt(4));
						        akeraioSBiy1row = Integer.valueOf(SBiy1row,2);
						        akeraioSBiy1column = Integer.valueOf(SBiy1column,2);
						       int stoixeioSBOX1 = akeraioSBiy1column +(akeraioSBiy1row*16);
						       y1 = S[w][stoixeioSBOX1];
						       
						       // *****y2 ******* ==>S(x2)
						       SBiy2row = Character.toString(x2.charAt(0)) + Character.toString(x2.charAt(5)) ;
						      
						        SBiy2column = Character.toString(x2.charAt(1)) + Character.toString(x2.charAt(2)) +Character.toString(x2.charAt(3)) + Character.toString(x2.charAt(4));
						   
						       akeraioSBiy2row = Integer.valueOf(SBiy2row,2);
						       akeraioSBiy2column = Integer.valueOf(SBiy2column,2);
						   
						       //XOR of S(x1) , S(x2) y1,y2
		                       stoixeio2SBOX1 = akeraioSBiy2column +(akeraioSBiy2row*16);
						       y2 = S[w][stoixeio2SBOX1];				       
						 
						       String SBxor = String.format("%06d", Integer.parseInt(Integer.toBinaryString(y1^y2)));
						
						       y1xory2 = Integer.parseInt(SBxor,2);
						       //XOR of inputs x1,x2
						        for(int a=0; a<6; a++)
						        {
						        	xoredvalues = Character.getNumericValue(x1.charAt(a) ^ Character.getNumericValue(x2.charAt(a)));
						        	xoredstring += Integer.toString(xoredvalues);
						      
						        }
						         x1xorx2 =Integer.parseInt(xoredstring,2);
						        x2 = Integer.toBinaryString(Integer.valueOf(x2, 2) + 1);
						        x2 = String.format("%06d", Integer.parseInt(x2));  
						    DDT[x1xorx2][y1xory2]++;//increment by one the element of the DDT table with row value x1(+)x2 and column value S(x1)(+)S(x2) = y1(+)y2
					    	}
					    	x1 = Integer.toBinaryString(Integer.valueOf(x1, 2) + 1);
					    }
					//calculating the biggest value in the DDT table considering it as L 
					//and the non-zero entries in column 1 aside from (0,0) element, considering as R
					 L=0;
					 R=0;
				
					for(int i =1; i<64; i++)
					{
						if(DDT[i][0] !=0 )
						{
							R++;
						}
						for (int j=0; j<16; j++)
						{
							if (DDT[i][j] > L)
							{
								L=DDT[i][j];
							}
						}
						
						
					}
					//S boxes are nxs = 4x6 elements
					
					Re[w] = ((double)(1- (L/Math.pow(2, n))))*(double)(1 -(R/(Math.pow(2, n))));
					System.out.println("Random S-Box "+(w+1));
					System.out.println("L:  " +L);
					System.out.println("R:  "+R);
					System.out.println("e   : " +Re[w]);
					}
					return Re;
	}
	
	
	
	public static void main(String args[]) {
		
	//DDT Table
		int DDT[][] = new int[64][16] ;
		
		double[] Re = RecommendedSboxesE();
	
		int x1xorx2;
		 int y1xory2 ;
		int stoixeio2SBOX1;
		int count = 0;
		String x1 = "000000";
		String x2;
		byte y1;
		byte y2;
		int xoredvalues = 0;
		int sxoredvalues = 0;
		String xoredstring = "";
		String sxoredstring = "";
		String SBiy1row;
		String SBiy1column;
		int akeraioSBiy1row;
		int akeraioSBiy1column;
		String SBiy2row;
		String SBiy2column;
		int akeraioSBiy2row;
		int akeraioSBiy2column;
		String SBiy2;
		String SBiy="";
		int	R=0;
		int	L=0;
		double	e[] = new double[8];
		int n=6;//S-box table of type nxs ,takes as input a group of 6bits (n) and gives output of 4bits(s)
		
		System.out.println("RANDOM GENERATED S-BOXES FOR THE ENCRYPTION-DECRYPTION OF PLAIN-TEXT USING DES ALGORITHM");
	    final byte[][] RS = new byte[8][64];
	  //creating 8 boxes with random numbers from 0 to 15
			sboxesGenerator(RS);
		//Kathe S box exei 64^64 pithana zeugaria eisodou ara 2 emfoleumena loop apo 1-64
			//Each pair of 6 bits inputs has 64x64  (64^2) possible pair of outputs so we use 2 loops from 1-64 one into the other
			for(int w=0; w<8; w++)
			{
				
				ddtrenewer(DDT);//calls the ddtrenewer function which fills all elements in DDT table with zeros
				 x1xorx2=0;
				  y1xory2=0; ;
				 stoixeio2SBOX1=0;
				 count = 0;
				 x1 = "000000";
				 x2="";
				 y1=0;
				 y2=0;
				 xoredvalues = 0;
				 sxoredvalues = 0;
				 xoredstring = "";
				 sxoredstring = "";
				 SBiy1row="";
				 SBiy1column="";
				 akeraioSBiy1row=0;
				 akeraioSBiy1column=0;
				 SBiy2row="";
				 SBiy2column="";
			     akeraioSBiy2row=0;
				 akeraioSBiy2column=0;
				 SBiy2="";
				 SBiy="";
				 R=0;
				 L=0;
				 
			 for(int i =0; i<64; i++)
			    {
			    	 x1 = String.format("%06d", Integer.parseInt(x1));//parsarw to string x1 san akeraio kai tou bazw midenika an dn exei 6 psifio stin arxi
					 x2 = "000000";
			    	for(int j=0; j<64; j++)
			    	{
			    		xoredstring = "";
					    count++;
				      //we take the first and the 6th bit of the inputs x1,x2 and we consider as SBiy1row the number of row that will address to the Sbox and SBiy1column the number of column that will address to the Sbox
				       
				        // ********  y1   ******** to S(x1) ,we calculate for each Sbox where the element is located and we find its value
				        SBiy1row = Character.toString(x1.charAt(0)) + Character.toString(x1.charAt(5)) ;
				        SBiy1column = Character.toString(x1.charAt(1)) + Character.toString(x1.charAt(2)) +Character.toString(x1.charAt(3)) + Character.toString(x1.charAt(4));
				       akeraioSBiy1row = Integer.valueOf(SBiy1row,2);
				       akeraioSBiy1column = Integer.valueOf(SBiy1column,2);
				       
				       int stoixeioSBOX1 = akeraioSBiy1column +(akeraioSBiy1row*16);
				       y1 = RS[w][stoixeioSBOX1];
				       
				       // *****y2 *******  S(x2)
				       SBiy2row = Character.toString(x2.charAt(0)) + Character.toString(x2.charAt(5)) ;
				        SBiy2column = Character.toString(x2.charAt(1)) + Character.toString(x2.charAt(2)) +Character.toString(x2.charAt(3)) + Character.toString(x2.charAt(4));
				       akeraioSBiy2row = Integer.valueOf(SBiy2row,2);
				       akeraioSBiy2column = Integer.valueOf(SBiy2column,2);
                       stoixeio2SBOX1 = akeraioSBiy2column +(akeraioSBiy2row*16);
				       y2 = RS[w][stoixeio2SBOX1];				       
				       String SBxor = String.format("%06d", Integer.parseInt(Integer.toBinaryString(y1^y2)));
				       y1xory2 = Integer.parseInt(SBxor,2);

				        for(int a=0; a<6; a++)
				        {
				        	xoredvalues = Character.getNumericValue(x1.charAt(a) ^ Character.getNumericValue(x2.charAt(a)));
				        	xoredstring += Integer.toString(xoredvalues);
				       
				        }
				 
				         x1xorx2 =Integer.parseInt(xoredstring,2);
				        x2 = Integer.toBinaryString(Integer.valueOf(x2, 2) + 1);
				        x2 = String.format("%06d", Integer.parseInt(x2));
				        
				
				        
				    DDT[x1xorx2][y1xory2]++;//increment by one the element of the DDT table with row value x1(+)x2 and column value S(x1)(+)S(x2) = y1(+)y2
				       
				        
				        
			    	}
			    	x1 = Integer.toBinaryString(Integer.valueOf(x1, 2) + 1);
			    }
			
			 
			    System.out.println("\n DDT TABLE" +(w+1)+ " GENERATED ");
			
			//prints the DDT Table
			DDTprinter(DDT);
			
			
			//calculating the biggest value in the DDT table considering it as L 
			//and the non-zero entries in column 1 aside from (0,0) element, considering as R
			 L=0;
			 R=0;
		
			for(int i =1; i<64; i++)
			{
				if(DDT[i][0] !=0 )
				{
					R++;
				}
				for (int j=0; j<16; j++)
				{
					if (DDT[i][j] > L)
					{
						L=DDT[i][j];
					}
				}
				
				
			}
			//S boxes are nxs = 6x4 elements which means they take as input a group of 6 bits and convert into a 4 bit group
		
			e[w] = ((double)(1- (L/Math.pow(2, n))))*(double)(1 -(R/(Math.pow(2, n))));
			System.out.println("L:  " +L);
			System.out.println("R:  "+R);
			System.out.println("e   : " +e[w]);
			}
			System.out.println("S-boxes comparison between the Random generated"
					+ "S boxes and the recommended ones");
			System.out.println("RECOMMENDED S BOX         RANDOM S BOX              RecSBox ==> RandomSBox");
			
					for(int i =0; i<8; i++)
					{
						System.out.println((i+1) +")" +Re[i] +"               "+e[i] + "                   "+ Math.floor(((Re[i]/e[i])*100)*100)/100 + "%");
					}
			
			
		String input ;
		String arg= null;
		do
		{
			
		System.out.println("Enter the plain text as a 16 character hexadecimal value :");
		Scanner scan = new Scanner(System.in);
	    input = scan.nextLine();
	    
	 
	    
		System.out.println("Length of input String: " +input.length());
		// input = new Scanner(System.in).nextLine();
		}
		
		while(input.length()<16);
		
		/*
		 Input conversion from string to hexadecimal in order to ask from the user a friendlier input not a hexadecimal
		 
		String output = new String(DatatypeConverter.parseHexBinary(input));
		*/
		
	
		
		
		//System.out.println(output);
		int inputBits[] = new int[64];
		// inputBits will store the 64 bits of the input as a an int array of
		// size 64. This program uses int arrays to store bits, for the sake
		// of simplicity. For efficient programming, use long data type. But
		// it increases program complexity which is unnecessary for this
		// context.
		for(int i=0 ; i < 16 ; i++) {
			// For every character in the 16 bit input, we get its binary value
			// by first parsing it into an int and then converting to a binary
			// string
			String s = Integer.toBinaryString(Integer.parseInt(input.charAt(i) + "", 16));
			
			// Java does not add padding zeros, i.e. 5 is returned as 111 but
			// we require 0111. Hence, this while loop adds padding 0's to the
			// binary value.
			while(s.length() < 4) {
				s = "0" + s;
			}
			// Add the 4 bits we have extracted into the array of bits.
			for(int j=0 ; j < 4 ; j++) {
				inputBits[(4*i)+j] = Integer.parseInt(s.charAt(j) + "");
			}
		}
		
		// Similar process is followed for the 16 bit key
		String key="";
		do
		{
			
			System.out.println("Enter the key as a 16 character hexadecimal value:");
			 key = new Scanner(System.in).nextLine();
	   
		System.out.println("Length of Key: " +key.length());
		// input = new Scanner(System.in).nextLine();
		}
		
		while(key.length()<16);
		
		
		int keyBits[] = new int[64];
		for(int i=0 ; i < 16 ; i++) {
			String s = Integer.toBinaryString(Integer.parseInt(key.charAt(i) + "", 16));
			while(s.length() < 4) {
				s = "0" + s;
			}
			for(int j=0 ; j < 4 ; j++) {
				keyBits[(4*i)+j] = Integer.parseInt(s.charAt(j) + "");
			}
		}
		
		// permute(int[] inputBits, int[] keyBits, boolean isDecrypt)
		// method is used here. This allows encryption and decryption to be
		// done in the same method, reducing code.
		System.out.println("\n+++ ENCRYPTION +++");
		int outputBits[] = permute(inputBits, keyBits, false, RS);
		System.out.println("\n+++ DECRYPTION +++");
		permute(outputBits, keyBits, true, RS);
	    }
	
	
	private static int[] permute(int[] inputBits, int[] keyBits, boolean isDecrypt,byte RS[][]) {
		// Initial permutation step takes input bits and permutes into the
		// newBits array
		int newBits[] = new int[inputBits.length];
		for(int i=0 ; i < inputBits.length ; i++) {
			newBits[i] = inputBits[IP[i]-1];
		}
		
		// 16 rounds will start here
		// L and R arrays are created to store the Left and Right halves of the
		// subkey respectively
		int L[] = new int[32];
		int R[] = new int[32];
		int i;
		
		// Permuted Choice 1 is done here
		for(i=0 ; i < 28 ; i++) {
			C[i] = keyBits[PC1[i]-1];
		}
		for( ; i < 56 ; i++) {
			D[i-28] = keyBits[PC1[i]-1];
		}
		
		// After PC1 the first L and R are ready to be used and hence looping
		// can start once L and R are initialized
		System.arraycopy(newBits, 0, L, 0, 32);
		System.arraycopy(newBits, 32, R, 0, 32);
		System.out.print("\nL0 = ");
		displayBits(L);
		System.out.print("R0 = ");
		displayBits(R);
		for(int n=0 ; n < 16 ; n++) {
			System.out.println("\n-------------");
			System.out.println("Round " + (n+1) + ":");
			// newR is the new R half generated by the Fiestel function. If it
			// is encrpytion then the KS method is called to generate the
			// subkey otherwise the stored subkeys are used in reverse order
			// for decryption.
			int newR[] = new int[0];
			if(isDecrypt) {
				newR = fiestel(R, subkey[15-n], RS);
				System.out.print("Round key = ");
				displayBits(subkey[15-n]);
			} else {
				newR = fiestel(R, KS(n, keyBits), RS);
				System.out.print("Round key = ");
				displayBits(subkey[n]);
			}
			// xor-ing the L and new R gives the new L value. new L is stored
			// in R and new R is stored in L, thus exchanging R and L for the
			// next round.
			int newL[] = xor(L, newR);
			L = R;
			R = newL;
			System.out.print("L = ");
			displayBits(L);
			System.out.print("R = ");
			displayBits(R);
		}
		
		// R and L has the two halves of the output before applying the final
		// permutation. This is called the "Preoutput".
		int output[] = new int[64];
		System.arraycopy(R, 0, output, 0, 32);
		System.arraycopy(L, 0, output, 32, 32);
		int finalOutput[] = new int[64];
		// Applying FP table to the preoutput, we get the final output:
		// Encryption => final output is ciphertext
		// Decryption => final output is plaintext
		for(i=0 ; i < 64 ; i++) {
			finalOutput[i] = output[FP[i]-1];
		}
		
		// Since the final output is stored as an int array of bits, we convert
		// it into a hex string:
		String hex = new String();
		for(i=0 ; i < 16 ; i++) {
			String bin = new String();
			for(int j=0 ; j < 4 ; j++) {
				bin += finalOutput[(4*i)+j];
			}
			int decimal = Integer.parseInt(bin, 2);
			hex += Integer.toHexString(decimal);
		}
		if(isDecrypt) {
			System.out.print("Decrypted text: ");
		
		} else {
			System.out.print("Encrypted text: ");
		}
		System.out.println(hex.toUpperCase());
		return finalOutput;
	}//end of permute function
	
	private static int[] KS(int round, int[] key) {
		// The KS (Key Structure) function generates the round keys.
		// C1 and D1 are the new values of C and D which will be generated in
		// this round.
		int C1[] = new int[28];
		int D1[] = new int[28];
		
		// The rotation array is used to set how many rotations are to be done
		int rotationTimes = (int) rotations[round];
		// leftShift() method is used for rotation (the rotation is basically)
		// a left shift operation, hence the name.
		C1 = leftShift(C, rotationTimes);
		D1 = leftShift(D, rotationTimes);
		// CnDn stores the combined C1 and D1 halves
		int CnDn[] = new int[56];
		System.arraycopy(C1, 0, CnDn, 0, 28);
		System.arraycopy(D1, 0, CnDn, 28, 28);
		// Kn stores the subkey, which is generated by applying the PC2 table
		// to CnDn
		int Kn[] = new int[48];
		for(int i=0 ; i < Kn.length ; i++) {
			Kn[i] = CnDn[PC2[i]-1];
		}
		
		// Now we store C1 and D1 in C and D respectively, thus becoming the
		// old C and D for the next round. Subkey is stored and returned.
		subkey[round] = Kn;
		C = C1;
		D = D1;
		return Kn;
	}//end of KS function
	
	private static int[] fiestel(int[] R, int[] roundKey, byte RS[][]) {
		// Method to implement Fiestel function.
		// First the 32 bits of the R array are expanded using E table.
		int expandedR[] = new int[48];
		for(int i=0 ; i < 48 ; i++) {
			expandedR[i] = R[E[i]-1];
		}
		// We xor the expanded R and the generated round key
		int temp[] = xor(expandedR, roundKey);
		// The S boxes are then applied to this xor result and this is the
		// output of the Fiestel function.
		int output[] = sBlock(temp,RS);
		return output;
	}//end of fiestel
	
	private static int[] xor(int[] a, int[] b) {
		// Simple xor function on two int arrays
		int answer[] = new int[a.length];
		for(int i=0 ; i < a.length ; i++) {
			answer[i] = a[i]^b[i];
		}
		return answer;
	}//end of xor function
	
	private static int[] sBlock(int[] bits,byte RS[][]) {
		// S-boxes are applied in this method.
		int output[] = new int[32];
		// We know that input will be of 32 bits, hence we will loop 32/4 = 8
		// times (divided by 4 as we will take 4 bits of input at each
		// iteration).
		for(int i=0 ; i < 8 ; i++) {
			// S-box requires a row and a column, which is found from the
			// input bits. The first and 6th bit of the current iteration
			// (i.e. bits 0 and 5) gives the row bits.
			int row[] = new int [2];
			row[0] = bits[6*i];
			row[1] = bits[(6*i)+5];
			String sRow = row[0] + "" + row[1];
			// Similarly column bits are found, which are the 4 bits between
			// the two row bits (i.e. bits 1,2,3,4)
			int column[] = new int[4];
			column[0] = bits[(6*i)+1];
			column[1] = bits[(6*i)+2];
			column[2] = bits[(6*i)+3];
			column[3] = bits[(6*i)+4];
			String sColumn = column[0] +""+ column[1] +""+ column[2] +""+ column[3];
			// Converting binary into decimal value, to be given into the
			// array as input
			int iRow = Integer.parseInt(sRow, 2);
			int iColumn = Integer.parseInt(sColumn, 2);
			int x = RS[i][(iRow*16) + iColumn];
			// We get decimal value of the S-box here, but we need to convert
			// it into binary:
			String s = Integer.toBinaryString(x);
			// Padding is required since Java returns a decimal '5' as '111' in
			// binary, when we require '0111'.
			while(s.length() < 4) {
				s = "0" + s;
			}
			// The binary bits are appended to the output
			for(int j=0 ; j < 4 ; j++) {
				output[(i*4) + j] = Integer.parseInt(s.charAt(j) + "");
			}
		}
		// P table is applied to the output and this is the final output of one
		// S-box round:
		int finalOutput[] = new int[32];
		for(int i=0 ; i < 32 ; i++) {
			finalOutput[i] = output[P[i]-1];
		}
		return finalOutput;
	}
	
	private static int[] leftShift(int[] bits, int n) {
		// Left shifting takes place here, i.e. each bit is rotated to the left
		// and the leftmost bit is stored at the rightmost bit. This is a left
		// shift operation.
		int answer[] = new int[bits.length];
		System.arraycopy(bits, 0, answer, 0, bits.length);
		for(int i=0 ; i < n ; i++) {
			int temp = answer[0];
			for(int j=0 ; j < bits.length-1 ; j++) {
				answer[j] = answer[j+1];
			}
			answer[bits.length-1] = temp;
		}
		return answer;
	}
	
	private static void displayBits(int[] bits) {
		// Method to display int array bits as a hexadecimal string.
		for(int i=0 ; i < bits.length ; i+=4) {
			String output = new String();
			for(int j=0 ; j < 4 ; j++) {
				output += bits[i+j];
			}
			System.out.print(Integer.toHexString(Integer.parseInt(output, 2)));
		}
		System.out.println();
	}
	
	private static void DDTprinter(int[][] DDT)
	{
		for(int i =0; i<64; i++)
		{
			
			for (int j=0; j<16; j++)
				
			{
				System.out.print(" "+DDT[i][j]);
			}
			System.out.println();
		}
	}
}
