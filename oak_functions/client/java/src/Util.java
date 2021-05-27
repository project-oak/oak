package com.google.oak.functions.client;

public class Util {
    /**
     * Concatenates two byte arrays.
     */
    static public byte[] concatenate(byte[] first, byte[] second) {
        byte[] result = new byte[first.length + second.length];
        System.arraycopy(first, 0, result, 0, first.length);
        System.arraycopy(second, 0, result, first.length, second.length);
        return result;
    }
}
