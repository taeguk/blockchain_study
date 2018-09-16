//
// Written in C++14 by taeguk (Taeguk Kwon <xornrbboy@gmail.com>)
//
// This is simple and readable implementation of SHA256.
// Don't use this in real world. It is written for just educational purpose.
//
// **IMPORTANT** This source code assumes it runs on little endian system.
//

#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

////////////////////////////////////////////////////////////////////////////////
// Basic Operations for SHA256
////////////////////////////////////////////////////////////////////////////////

uint32_t ChangeEndian(uint32_t x)
{
    x = ((x << 8) & 0xFF00FF00) | ((x >> 8) & 0xFF00FF);
    return (x << 16) | (x >> 16);
}

uint64_t ChangeEndian(uint64_t x)
{
    x = ((x <<  8) & 0xFF00FF00FF00FF00ULL) | ((x >>  8) & 0x00FF00FF00FF00FFULL);
    x = ((x << 16) & 0xFFFF0000FFFF0000ULL) | ((x >> 16) & 0x0000FFFF0000FFFFULL);
    return (x << 32) | (x >> 32);
}

uint32_t RotateRight(uint32_t x, uint32_t n)
{
    return (x >> n) | (x << (32 - n));
}

// σ0 (Small Sigma 0)
uint32_t SSigma_0(uint32_t x)
{
    return RotateRight(x, 7) ^ RotateRight(x, 18) ^ (x >> 3);
}

// σ1 (Small Sigma 1)
uint32_t SSigma_1(uint32_t x)
{
    return RotateRight(x, 17) ^ RotateRight(x, 19) ^ (x >> 10);
}

// Σ0 (Big Sigma 0)
uint32_t BSigma_0(uint32_t x)
{
    return RotateRight(x, 2) ^ RotateRight(x, 13) ^ RotateRight(x, 22);
}

// Σ1 (Big Sigma 1)
uint32_t BSigma_1(uint32_t x)
{
    return RotateRight(x, 6) ^ RotateRight(x, 11) ^ RotateRight(x, 25);
}

// Let X, Y, Z to a bit of x, y, z each.
// If X == 1, take Y. Otherwise take Z.
uint32_t Choose(uint32_t x, uint32_t y, uint32_t z)
{
    return (x & y) ^ (~x & z);
}

// Let X, Y, Z to a bit of x, y, z each.
// Take a bit of majority among X, Y, and Z.
uint32_t Majority(uint32_t x, uint32_t y, uint32_t z)
{
    return (x & y) ^ (x & z) ^ (y & z);
}

////////////////////////////////////////////////////////////////////////////////
// Core Functions of SHA256
////////////////////////////////////////////////////////////////////////////////

std::array<uint32_t, 8> Make_H0()
{
    const double kPrimeList[] = { 2, 3, 5, 7, 11, 13, 17, 19 };
    static_assert(sizeof(kPrimeList) / sizeof(*kPrimeList) == 8, "");

    std::array<uint32_t, 8> H;

    for (int i = 0; i < 8; ++i)
    {
        auto v = std::sqrt(kPrimeList[i]);

        v -= static_cast<uint32_t>(v);
        v *= std::pow(16, 8);

        H[i] = static_cast<uint32_t>(v);
    }

    return H;
}

std::array<uint32_t, 64> Make_K()
{
    double kPrimeList[] = {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
        31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
        179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
        233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
        283, 293, 307, 311
    };
    static_assert(sizeof(kPrimeList) / sizeof(*kPrimeList) == 64, "");

    std::array<uint32_t, 64> K;

    for (int i = 0; i < 64; ++i)
    {
        auto v = std::cbrt(kPrimeList[i]);

        v -= static_cast<uint32_t>(v);
        v *= std::pow(16, 8);

        K[i] = static_cast<uint32_t>(v);
    }

    return K;
}

std::array<uint32_t, 64> Make_W(const uint8_t (&M)[64])
{
    std::array<uint32_t, 64> W;

    for (int i = 0; i < 16; ++i)
    {
        W[i] = ChangeEndian(reinterpret_cast<uint32_t const&>(M[i * 4]));
    }

    for (int i = 16; i < 64; ++i)
    {
        // MEXP (Message Expansion Function)
        W[i] = SSigma_1(W[i - 2]) + W[i - 7] + SSigma_0(W[i - 15]) + W[i - 16];
    }

    return W;
}

std::array<uint32_t, 8> Round(std::array<uint32_t, 8> const& H, uint32_t K, uint32_t W)
{
    std::array<uint32_t, 8> nH; // next H

    auto maj = Majority(H[0], H[1], H[2]);
    auto ch = Choose(H[4], H[5], H[6]);
    auto s = K + BSigma_1(H[4]) + ch + H[7] + W;

    nH[0] = BSigma_0(H[0]) + maj + s;
    nH[1] = H[0];
    nH[2] = H[1];
    nH[3] = H[2];
    nH[4] = H[3] + s;
    nH[5] = H[4];
    nH[6] = H[5];
    nH[7] = H[6];

    return nH;
}

////////////////////////////////////////////////////////////////////////////////
// Implementation of SHA256
////////////////////////////////////////////////////////////////////////////////

// Add padding to message.
void PreProcess(std::vector<uint8_t>& message)
{
    auto L = static_cast<uint64_t>(message.size());

    // Append single '1' bit and seven '0' bits.
    message.push_back(0b10000000);

    // Append (K * 8) '0' bits, where L + 1 + K + 8 is a multiple of 64.
    auto K = 64 - (((L % 64) + 9) % 64);
    if (K == 64) K = 0;

    for (int i = 0; i < K; ++i)
    {
        message.push_back(0);
    }

    // Append the bit length of original message.
    assert(L <= UINT64_MAX / 8);
    uint64_t bitLengthInBigEndian = ChangeEndian(L * 8);
    auto ptr = reinterpret_cast<uint8_t*>(&bitLengthInBigEndian);

    message.insert(std::end(message), ptr, ptr + 8);
    assert(message.size() % 64 == 0);
}

std::array<uint32_t, 8> Process(std::vector<uint8_t> const& message)
{
    assert(message.size() % 64 == 0);

    const auto K = Make_K();
    const auto blockCount = message.size() / 64;

    auto digest = Make_H0();

    for (int i = 0; i < blockCount; ++i)
    {
        auto W = Make_W(reinterpret_cast<const uint8_t(&)[64]>(message[i * 64]));
        auto H = digest;

        for (int r = 0; r < 64; ++r)
        {
            H = Round(H, K[r], W[r]);
        }

        for (int i = 0; i < 8; ++i)
        {
            digest[i] += H[i];
        }
    }

    return digest;
}

////////////////////////////////////////////////////////////////////////////////

std::string Hexify(std::array<uint32_t, 8> const& digest)
{
    std::stringstream stream;

    for (auto x : digest)
    {
        stream << std::setfill('0') << std::setw(8) << std::hex << x;
    }

    return stream.str();
}

std::string SHA256(std::vector<uint8_t> message)
{
    PreProcess(message);
    auto digest = Process(message);
    return Hexify(digest);
}

void ShowUsage(char const* programPath)
{
    assert(programPath);
    printf("Usage #1: %s <the file path to be hashed>\n", programPath);
    printf("Usage #2: %s -s <the string to be hashed>\n", programPath);
}

int main(int argc, char* argv[])
{
    if (argc < 2)
    {
        ShowUsage(argv[0]);
        return 1;
    }

    if (argv[1] == std::string("-s"))
    {
        if (argc < 3)
        {
            ShowUsage(argv[0]);
            return 1;
        }

        // Hash the given string.
        std::string str(argv[2]);
        std::vector<uint8_t> message(std::begin(str), std::end(str));
        std::cout << SHA256(std::move(message)) << std::endl;
    }
    else
    {
        // Hash the given file.
        std::string filePath(argv[1]);
        std::ifstream ifs(filePath, std::ios::in | std::ios::binary);

        if (!ifs.is_open())
        {
            printf("Cannot open the file \"%s\".\n", filePath.c_str());
            return 1;
        }

        std::vector<uint8_t> content((std::istreambuf_iterator<char>(ifs)),
                                      std::istreambuf_iterator<char>());

        std::cout << SHA256(std::move(content)) << std::endl;
    }
}
