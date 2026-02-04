import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class CrackKeys {
    private static List<String> plainTexts = new ArrayList<>();
    private static List<String> cipherTexts = new ArrayList<>();
    private static int L0,R0,L4,R4;
    private static List<List<Integer>> result = new LinkedList<>();
    static void readFile() throws IOException {
        BufferedReader br = new BufferedReader(new FileReader("known.txt"));
        String line;

        while ((line = br.readLine()) != null) {
            String line2 = br.readLine();
            br.readLine();

            if (line2 == null)
                break;

            String plainText = line.split("=")[1].trim();
            String cipherText = line2.split("=")[1].trim();

            plainTexts.add(plainText);
            cipherTexts.add(cipherText);
        }

        br.close();
    }
    private static int expandInner12BitKey(int k) {
        return (((k >> 6) & 0x3F) << 16) + ((k & 0x3F) << 8) ;
    }

    private static int expandOuter20BitKey(int k, int innerKey) {
        int a0 = (((k & 0xF) >> 2) << 6) + ((innerKey >> 16) & 0xFF);
        int a1 = ((k & 0x3) << 6) + ((innerKey >> 8) & 0xFF);
        int b0 = (k >> 12) & 0xFF;
        int b3 = (k >> 4) & 0xFF;
        int b1 = b0^a0;
        int b2 = b3^a1;
        return (b0 << 24)  + (b1 << 16) + (b2 << 8) + b3;
    }
    private static void loadPairs(int wordIndex) {
        L0 = (int) Long.parseLong(plainTexts.get(wordIndex).substring(0,8), 16);
        R0 = (int) Long.parseLong(plainTexts.get(wordIndex).substring(8), 16);
        L4 = (int) Long.parseLong(cipherTexts.get(wordIndex).substring(0,8), 16);
        R4 = (int) Long.parseLong(cipherTexts.get(wordIndex).substring(8), 16);
    }
    private static int getNthBit(int num, int n) {
        return (num >> (31-n)) & 1;
    }


    static int s(int num, int... positions) {
        int val = 0;
        for (int p : positions) val ^= getNthBit(num, p);
        return val;
    }
    private static int getConstForInner12BitsK0(int k0,int w)
    {
        loadPairs(w);
        int a1 = s(L0^R0^L4,5,13,21);
        int a2 = s(L0^L4^R4, 15);
        int a3 = s(FEAL.f(L0^R0^k0), 15);

        return a1^a2^a3;
    }
    private static int getConstFor20BitsK0(int k0,int w)
    {
        loadPairs(w);
        int a1 = s(L0^R0^L4,13);
        int a2 = s(L0^L4^R4, 7,15,23,31);
        int a3 = s(FEAL.f(L0^R0^k0), 7,15,23,31);
        return a1^a2^a3;
    }
    public static int getConstForInner12BitsK1(int k0,int k1,int w)
    {
        loadPairs(w);
        int a1 = s(L0^L4^R4,5,13,21);
        int f1 = FEAL.f(L0^R0^k0);
        int a2 = s(FEAL.f(L0^f1^k1), 15);
        return a1^a2;
    }
    public static int getConstFor20BitsK1(int k0, int k1, int w)
    {
        loadPairs(w);
        int a1 = s(L0^L4^R4,13);
        int f1 = FEAL.f(L0^R0^k0);
        int a2 = s(FEAL.f(L0^f1^k1), 7,15,23,31);
        return a1^a2;
    }
    public static int getConstForInner12BitsK2(int k0,int k1,int k2,int w)
    {
        loadPairs(w);
        int a1 = s(L0^R0^L4,5,13,21);
        int y0 = FEAL.f(L0^R0^k0);
        int y1 = FEAL.f(L0^y0^k1);
        int a2 = s(FEAL.f(L0^R0^y1^k2),15);
        return a1^a2;
    }
    public static int getConstFor20BitsK2(int k0, int k1, int k2, int w)
    {
        loadPairs(w);
        int a1 = s(L0^R0^L4,13);
        int y0 = FEAL.f(L0^R0^k0);
        int y1 = FEAL.f(L0^y0^k1);
        int a2 = s(FEAL.f(L0^R0^y1^k2),7,15,23,31);
        return a1^a2;
    }
    public static int getConstForInner12BitK3(int k0,int k1,int k2,int k3,int w)
    {
        loadPairs(w);
        int a1 = s(L0^L4^R4,5,13,21);
        int a2 = s(L0^R0^L4, 15);
        int y0 = FEAL.f(L0^R0^k0);
        int y1 = FEAL.f(L0^y0^k1);
        int y2 = FEAL.f(L0^R0^y1^k2);
        int a3 = s(FEAL.f(L0^y0^y2^k3), 15);
        return a1^a2^a3;
    }
    public static int getConstFor20BitsK3(int k0, int k1, int k2, int k3, int w)
    {
        loadPairs(w);
        int a1 = s(L0^L4^R4,13);
        int a2 = s(L0^R0^L4, 7,15,23,31);
        int y0 = FEAL.f(L0^R0^k0);
        int y1 = FEAL.f(L0^y0^k1);
        int y2 = FEAL.f(L0^R0^y1^k2);
        int a3 = s(FEAL.f(L0^y0^y2^k3), 7,15,23,31);
        return a1^a2^a3;
    }
    public static void findOtherKeysAndTest(int k0,int k1,int k2,int k3){
        int Y0 = FEAL.f(L0^R0^k0);
        int Y1 = FEAL.f(L0^Y0^k1);
        int Y2 = FEAL.f(L0^R0^Y1^k2);
        int Y3 = FEAL.f(L0^Y0^Y2^k3);
        int k4 = L4^L0^R0^Y1^Y3;
        int k5 = L0^Y0^Y2^L4^k4^R4;
        int[] keys = {k0,k1,k2,k3,k4,k5};
        byte[] data = new byte[8];
        for(int i=0;i<plainTexts.size();i++){
            for (int j=0;j<8;j++)
            {
                data[j] = (byte)(Integer.parseInt(cipherTexts.get(i).substring(j * 2, (j * 2) + 2),16)&255);
            }
            FEAL.decrypt(data,keys);
            StringBuilder sb = new StringBuilder(16);
            for(int j=0;j<8;j++)
            {
                sb.append(String.format("%02x",data[j]));
            }
            if(!plainTexts.get(i).equals(sb.toString())){
                return;
            }
        }
        List<Integer> list = new ArrayList<>(6);
        list.add(k0);
        list.add(k1);
        list.add(k2);
        list.add(k3);
        list.add(k4);
        list.add(k5);
        result.add(list);
        try {
            System.out.println("0x" + Integer.toHexString(k0) + "\t0x" + Integer.toHexString(k1) + "\t0x" + Integer.toHexString(k2) + "\t0x" + Integer.toHexString(k3) + "\t0x" + Integer.toHexString(k4) + "\t0x" + Integer.toHexString(k5));
        } catch (Exception e) {
            System.out.println("Unable to write file...");
        }
        
    }

    public static void printResultPattern()
    {
        for(int i=0;i<6;i++)
        {
            System.out.println("Key "+i+":");
            StringBuilder sb = new StringBuilder(32);
            for(int j=0;j<32;j++)
            {
                int key = result.get(0).get(i);
                int bit1 = getNthBit(key,j);
                for(int k=1;k<result.size();k++)
                {
                    key = result.get(k).get(i);
                    int bit2 = getNthBit(key,j);
                    if(bit1!=bit2)
                    {
                        sb.append("x");
                        break;
                    }
                    if(k==result.size()-1)
                    {
                        sb.append(bit1);
                    }
                }
            }
            System.out.println(sb.toString());
        }
    }

    public static void attackK3(int k0,int k1,int k2)
    {
        for(int k3=0;k3<4096;k3++)
        {
            int innerKey = expandInner12BitKey(k3);
            int innerConst = getConstForInner12BitK3(k0,k1,k2,innerKey,0);
            for(int i=1;i<plainTexts.size();i++)
            {
                int innerConst1 = getConstForInner12BitK3(k0,k1,k2,innerKey,i);
                if(innerConst!=innerConst1)
                {
                    break;
                }
                if(i==plainTexts.size()-1)
                {
                    for(int j=0;j<1048576;j++)
                    {
                        int fullKey = expandOuter20BitKey(j,innerKey);
                        int outerConst = getConstFor20BitsK3(k0,k1,k2,fullKey,0);
                        for(int k=1;k<plainTexts.size();k++)
                        {
                            int outerConst1 = getConstFor20BitsK3(k0,k1,k2,fullKey,k);
                            if(outerConst!=outerConst1)
                            {
                                break;
                            }
                            if(k==plainTexts.size()-1)
                            {

                                findOtherKeysAndTest(k0,k1,k2,fullKey);
                            }
                        }
                    }
                }
            }
        }
    }
    public static void attackK2(int k0,int k1)
    {
        for(int k2=0;k2<4096;k2++)
        {
            int innerKey = expandInner12BitKey(k2);
            int innerConst = getConstForInner12BitsK2(k0,k1,innerKey,0);
            for(int i=1;i<plainTexts.size();i++)
            {
                int innerConst1 = getConstForInner12BitsK2(k0,k1,innerKey,i);
                if(innerConst!=innerConst1)
                {
                    break;
                }
                if(i==plainTexts.size()-1)
                {
                    for(int j=0;j<1048576;j++)
                    {
                        int fullKey = expandOuter20BitKey(j,innerKey);
                        int outerConst = getConstFor20BitsK2(k0,k1,fullKey,0);
                        for(int k=1;k<plainTexts.size();k++)
                        {
                            int outerConst1 = getConstFor20BitsK2(k0,k1,fullKey,k);
                            if(outerConst!=outerConst1)
                            {
                                break;
                            }
                            if(k==plainTexts.size()-1)
                            {
                                attackK3(k0,k1,fullKey);
                            }
                        }
                    }
                }
            }
        }

    }
    public static void attackK1(int k0)
    {
        for(int k1=0;k1<4096;k1++)
        {
            int innerKey = expandInner12BitKey(k1);
            int constVal = getConstForInner12BitsK1(k0,innerKey,0);
            for(int w=1;w<plainTexts.size();w++)
            {
                int constVal1=getConstForInner12BitsK1(k0,innerKey,w);
                if(constVal1!=constVal)
                {
                    break;
                }
                if(w == plainTexts.size()-1)
                {
                    for(int i=0;i<1048576;i++)
                    {
                        int fullKey = expandOuter20BitKey(i,innerKey);
                        int fullConstVal1= getConstFor20BitsK1(k0,fullKey,0);
                        for(int j=1;j<plainTexts.size();j++)
                        {
                            int fullConstVal2= getConstFor20BitsK1(k0,fullKey,j);
                            if (fullConstVal1!=fullConstVal2)
                            {
                                break;
                            }
                            if (j==plainTexts.size()-1)
                            {
                                attackK2(k0,fullKey);
                            }
                        }
                    }
                }
            }
        }
    }
    public static void main(String[] args) throws Exception {
        readFile();
        for(int k0=0;k0<4096;k0++)
        {
            int innerKey = expandInner12BitKey(k0);
            int constVal = getConstForInner12BitsK0(innerKey, 0);
            for(int w=1;w<plainTexts.size();w++)
            {
                int constVal1 = getConstForInner12BitsK0(innerKey, w);
                if(constVal1 != constVal)
                {
                    break;
                }
                if(w==plainTexts.size()-1)
                {
                    for(int i=0;i<1048576;i++){
                        int fullKey = expandOuter20BitKey(i,innerKey);
                        int fullConst = getConstFor20BitsK0(fullKey, 0);
                        for(int j=1;j<plainTexts.size();j++)
                        {
                            int fullConst1 = getConstFor20BitsK0(fullKey, j);
                            if(fullConst1 != fullConst)
                            {
                                break;
                            }
                            if(j==plainTexts.size()-1)
                            {
                                attackK1(fullKey);
                            }

                        }
                    }
                }
            }
        }
        printResultPattern();
    }
}
