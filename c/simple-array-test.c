#include<stdio.h>

double foo (double x)
{

  double sensor_data[] = {
    20.79148, 20.09775, 19.42749, 19.60912, 19.37787, 21.47362, 30.42308,
    38.58739, 50.17102, 58.30209, 69.96654, 79.27626, 90.44830, 101.32235};

        double m;            // Measurement
        double y;            // Residual of estimation
        double K;            // Kalman Gain
        double t     =  5.0; // Time between measurements
        double temp  = 18.0; // Initial guess temperature
  const double rate  =  0.2; // Initial guess heating rate
        double p_var = 25.0; // Temp estimation variance
  const double r_var =  1.0; // Measurement noise variance
  const double q_s   = 0.25; // Process noise variance, stable
  const double q_h   =  5.0; // Process noise variance, heating
        double q     =  q_s; // Measurement noise variance

  for(int i = 0; i < 14; i ++) {
    m          = sensor_data[i];
    // Update
    y          = m - temp;
    K          = p_var / (p_var + r_var); // S simplifies to (p + r)
    temp       = temp + K * y;
    p_var      = (1.0 - K) * p_var;
    // Predict
    temp       = temp + t * rate;
    p_var      = p_var + q;
    // Adapt
    if (y * y > 5.0 * (p_var + r_var)) { // uncertainty exceeds 5 std deviations
      q = q_h;
    } else {
      q = q_s;
    }
  }
  return temp;
  /*
    double as[] = {
        20.79148, 20.09775, 19.42749, 19.60912, 19.37787, 21.47362, 30.42308,
        38.58739, 50.17102, 58.30209, 69.96654, 79.27626, 90.44830, 101.32235
    };

    double x = 0.0;

    for (int i = 0; i < 1; i++) {
        x = x + as[i];
    }

    //x = x / 14.0;
    return x;
    */
}

int main() {
    double a = foo(-10);
    printf("%f\n", a);
}
