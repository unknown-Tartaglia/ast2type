/*
 *@Date: 2022-01-05 10:19:43
 *@Description: 个人中心固定资产
 */
import React, { Component } from 'react';
import { Text, TouchableOpacity, View } from 'react-native';
import {
  CommonUtils,
  PlatformUtils,
  RouterUtils,
  t,
  WithTheme,
  monitor,
  itemExposeHoc,
  Service as env,
  LoginUtils,
  DarkStore,
  ScreenUtils,
} from '@hw-vmall/vrn-basic-comp';
import { SvgIcon } from '@hw-vmall/vrn-bussiness-comp';
import dapReportList from './dapReportList';
import Styles from './style/index';

interface Props {
  styleNew?: any;
  personaPc?: boolean;
  imgHeight?: number;
  clickItem: any;
  isLogin: any;
  lang: any;
  isRefresh: any;
  isRefreshTab: any;
  integralt: any;
  personalData: any;
}
interface Stste {
  isLoginState: boolean;
  apkGotourl: any;
  isLogin: boolean;
}
class indexAsster extends Component<Props, Stste> {
  bool: boolean;
  widthOld: any;
  eventListener: any;
  switchTabLinstener: any;
  linkFinished: boolean;
  gotourl: string;
  apkGotourl: any;
  constructor(props) {
    super(props);
    this.state = {
      isLoginState: false,
      apkGotourl: '',
      isLogin: this.props.isLogin,
    };
    this.linkFinished = true;
  }

  componentWillReceiveProps(nextProps): void {
    this.setState({
      isLogin: nextProps.isLogin,
    });
  }

  componentDidMount() {
    this.eventListener = LoginUtils.listenLoginStatus((isLogin: boolean) => {
      if (isLogin === false && this.linkFinished === false) {
        this.setState(
          {
            isLoginState: isLogin,
          },
          () => {
            this.linkFinished = true;
            this.apkGotourl = '';
          },
        );
      }
    });
  }
  componentWillUnmount() {
    this.eventListener?.remove();
  }

  isPc = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };

  isApk = () => {
    return PlatformUtils.isApp();
  };

  isPcPad = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width) || ScreenUtils.isMedium(width);
  };

  switchClick = (key) => {
    const ISURL = PlatformUtils.isIOS() ? 'pointmallios' : 'pointmall';
    switch (key) {
      case 'integralt':
        if (this.isApk()) {
          return `vmall://com.vmall.client/home/activity?isShowLayout=false&pn=${ISURL}`;
        } else if (this.isPc()) {
          return env.webDomain + 'member/newpoint'
        } else {
          return `${env.webDomain}portal/activity/index.html?isShowLayout=false&pn=pointmall`;
        }
      case 'coupon':
        if (this.isApk()) {
          return 'vmall://com.vmall.client/product/couponlist';
        } else if (this.isPc()) {
          return env.webDomain + 'member/coupon';
        } else {
          return env.wapDomain + 'member/coupon';
        }
      case 'voucher':
        if (this.isApk()) {
          return 'vmall://com.vmall.client/mine/voucher';
        } else if (this.isPc()) {
          return env.webDomain + 'member/balance';
        } else {
          return env.wapDomain + 'voucher/detail';
        }
      default:
        break;
    }
  };
  onPressClick = (key) => {
    let context;
    let numClick;
    let index;
    let name;
    this.gotourl = this.switchClick(key);

    this.apkGotourl = this.switchClick(key);
    const { isLogin } = this.props;
    const tmpKey = String(key);
    if (isLogin) {
      // '110000101/210000101/310000101
      if (tmpKey === 'integralt') {
        context = '点击积分图标';
        index = 7;
        name = '积分';
      } else if (tmpKey === 'coupon') {
        context = '点击优惠券图标';
        index = 8;
        name = '优惠券';
      } else {
        context = '点击代金券图标';
        index = 9;
        name = '代金券';
      }
      const { clickItem } = this.props;
      numClick = this.isPc() ? '310000101' : '210000101';
      numClick = this.isApk() ? '110000101' : numClick;
      clickItem(context, numClick, this.gotourl, index, name);
      RouterUtils.gotoPage(this.gotourl);
    } else {
      if (tmpKey === 'integralt') {
        context = '点击积分图标';
        name = '积分';
        index = 7;
      } else if (tmpKey === 'coupon') {
        context = '点击优惠券图标';
        name = '优惠券';
        index = 8;
      } else {
        context = '点击代金券图标';
        name = '代金券';
        index = 9;
      }
      numClick = this.isPc() ? '310000101' : '210000101';
      numClick = this.isApk() ? '110000101' : numClick;
      if (this.isApk()) {
        this.eventListener = LoginUtils.listenLoginStatus((login: boolean) => {
          if (login === true && this.linkFinished === true) {
            this.setState(
              {
                isLoginState: login,
              },
              () => {
                this.linkFinished = false;
                RouterUtils.gotoPage(this.apkGotourl);
              },
            );
          }
        });
        const url = 'vmall://com.vmall.client/home/login';
        const { clickItem } = this.props;
        clickItem(context, numClick, url, index, name);
        RouterUtils.gotoPage(url);
      } else {
        // 添加后缀，重定向
        const gotourl = encodeURIComponent(this.gotourl);
        const loginUrl = this.isPc()
          ? `${env.webDomain}account/login?url=${gotourl}`
          : `${env.wapDomain}account/applogin?url=${gotourl}`;
        const { clickItem } = this.props;
        clickItem(context, numClick, loginUrl, index, name);
        RouterUtils.gotoPage(loginUrl);
      }
    }
  };
  // 渲染箭头
  renderArrow = () => {
    return (
      <View style={{ marginLeft: 7 }}>
        <SvgIcon
          iconName={'ic24-more'}
          width="12"
          height="24"
          normalCol={DarkStore.theme.C24.color}
          opacity={DarkStore.theme.C24.opacity}
        />
      </View>
    );
  };

  render() {
    const { isLogin } = this.state;
    const { personalData, personaPc = false } = this.props;
    // 语言处理
    const showLang = this.props.lang === 'zh-CN';
    const TopStyle = {
      marginBottom: this.isPc() ? 0 : 2,
    };
    // 竖线
    const styleLine = {
      height: personaPc ? 32 : 24,
      marginHorizontal: personaPc ? 17 : 12,
    };
    const params = {
      personaPc,
      isLogin,
      personalData,
      showLang,
      TopStyle,
    }
    return (
      <WithTheme themeStyles={Styles}>
        {(_styles) => {
          return (
            <View style={[_styles.cardbgdefa, this.props.styleNew]}>
              {/* 积分 */}
              {this.renderIntegralt(params, _styles)}
              {/* 竖线 */}
              <View style={[styleLine, _styles.splitline]} />
              {/* 优惠券 */}
              {this.renderCoupon(params, _styles)}
              {/* 竖线 */}
              <View style={[styleLine, _styles.splitline]} />
              {/* 代金券 */}
              <TouchableOpacity
                activeOpacity={1}
                onPress={() => this.onPressClick('voucher')}
                style={[
                  personaPc ? _styles.itemPadDefaul : _styles.itemdefaul,
                  !this.isPcPad() && {
                    paddingRight: 12,
                    paddingLeft: 0,
                  },
                ]}
              >
                <View style={[this.isPcPad() ? _styles.itemChild : _styles.itemChildwap]}>
                  {isLogin ? (
                    <Text style={[personaPc ? _styles.numTextPc : _styles.numText]}>
                      {personalData.voucher || String(personalData.voucher) === '0' ? personalData.voucher : personalData.symbol}
                    </Text>
                  ) : (
                    <Text style={[!personaPc ? _styles.numTextNo : _styles.numSymbolPc]}>{personalData.symbol}</Text>
                  )}
                  <View style={_styles.bonusContainer}>
                    {/* vouchers */}
                    {!showLang && this.isApk() ? (
                      <Text
                        ellipsizeMode={'tail'}
                        numberOfLines={2}
                        style={[personaPc ? _styles.wordsTextPcTwo : _styles.wordsTextTwo, TopStyle]}
                      >
                        {t('vouchers')}
                      </Text>
                    ) : (
                      <Text style={[personaPc ? _styles.wordsTextPc : _styles.wordsText, TopStyle]}>
                        {t('vouchers')}
                      </Text>
                    )}
                    {this.renderArrow()}
                  </View>
                </View>
              </TouchableOpacity>
            </View>
          );
        }}
      </WithTheme>
    );
  }

  private renderCoupon(params: any, _styles: any) {
    const {
      personaPc,
      isLogin,
      personalData,
      showLang,
      TopStyle,
    } = params;
    return <TouchableOpacity
      activeOpacity={1}
      onPress={() => this.onPressClick('coupon')}
      style={[
        personaPc ? _styles.itemPadDefaul : _styles.itemdefaul,
        { paddingRight: personaPc ? 0 : 12.5 },
      ]}
    >
      <View style={[this.isPcPad() ? _styles.itemChild : _styles.itemChildwap]}>
        {isLogin ? (
          <Text style={[personaPc ? _styles.numTextPc : _styles.numText]}>
            {personalData.coupon || String(personalData.coupon) === '0' ? personalData.coupon : personalData.symbol}
          </Text>
        ) : (
          <Text style={[personaPc ? _styles.numSymbolPc : _styles.numTextNo]}>{personalData.symbol}</Text>
        )}
        <View style={_styles.bonusContainer}>
          {/* Coupons */}
          {!showLang && this.isApk() ? (
            <Text
              numberOfLines={2}
              ellipsizeMode={'tail'}
              style={[personaPc ? _styles.wordsTextPcTwo : _styles.wordsTextTwo, TopStyle]}
            >
              {t('coupons')}
            </Text>
          ) : (
            <Text style={[personaPc ? _styles.wordsTextPc : _styles.wordsText, TopStyle]}>
              {t('coupons')}
            </Text>
          )}
          {this.renderArrow()}
        </View>
      </View>
    </TouchableOpacity>;
  }

  private renderIntegralt(params: any, _styles: any) {
    const {
      personaPc,
      isLogin,
      personalData,
      showLang,
      TopStyle,
    } = params;
    return <TouchableOpacity
      activeOpacity={1}
      onPress={() => this.onPressClick('integralt')}
      style={[
        personaPc ? _styles.itemPadDefaul : _styles.itemdefaul,
        { paddingRight: personaPc ? 0 : 12.5 },
      ]}
    >
      <View style={[this.isPcPad() ? _styles.itemChild : _styles.itemChildwap]}>
        {isLogin ? (
          <Text style={[personaPc ? _styles.numTextPc : _styles.numText]}>
            {personalData.integralt || String(personalData.integralt) === '0'
              ? personalData.integralt
              : personalData.symbol}
          </Text>
        ) : (
          <Text style={[personaPc ? _styles.numSymbolPc : _styles.numTextNo]}>{personalData.symbol}</Text>
        )}
        <View style={_styles.bonusContainer}>
          {/* 词条bonus points */}
          {!showLang && this.isApk() ? (
            <Text
              style={[personaPc ? _styles.wordsTextPcTwo : _styles.wordsTextTwo, TopStyle]}
              numberOfLines={2}
              ellipsizeMode={'tail'}
            >
              {t('integral')}
            </Text>
          ) : (
            <Text style={[personaPc ? _styles.wordsTextPc : _styles.wordsText, TopStyle]}>
              {t('integral')}
            </Text>
          )}
          {this.renderArrow()}
        </View>
      </View>
    </TouchableOpacity>;
  }
}
export default monitor(dapReportList)(itemExposeHoc(indexAsster));
