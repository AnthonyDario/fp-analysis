// From Solovyev et al. FPTaylor
int foo(double a, double b) {
    double r;
    if (b >= a) {
        r = b / (b - a + 0.5);
    } else {
        r =  b / 0.5;
    }
    return 0;
}

int main() {
}
