void foo (double a)
{
    double as[] = {
        20.79148, 20.09775, 19.42749, 19.60912, 19.37787, 21.47362, 30.42308,
        38.58739, 50.17102, 58.30209, 69.96654, 79.27626, 90.44830, 101.32235
    };

    double x = 0.0;

    for (int i = 0; i < 14; i++) {
        x = x + a * as[i];
    }

    x = x / 14.0;
}

int main() {
    foo(2.2);
}
